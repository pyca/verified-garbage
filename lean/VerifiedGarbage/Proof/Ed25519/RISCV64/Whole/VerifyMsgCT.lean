module

import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.Challenge
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyCT
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Prune
meta import VerifiedGarbage.Proof.Ed25519.Challenge
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyFn
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify

/-! ### `Ed25519.RISCV64.Whole.VerifyMsg`, which only this module used -/

section

/-! ### `Ed25519.RISCV64.Whole.VerifyHash`, which only this module used -/

section

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

/-- The static of the cached `-[1]B … -[15]B`, which `verify_equation` reads. -/
abbrev vtbR (s : State) : Region := ⟨s.syms Impl.Ed25519.RISCV64.bSym, 1920⟩

/-- The precondition, by register, with the static `vtbR` of `verify_equation`. -/
structure VerPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 32⟩, vmsgR s, ⟨s.gpr .a3, 64⟩, vtbR s]
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
  tfit : (s.syms Impl.Ed25519.RISCV64.bSym).toNat + 1920 ≤ 2 ^ 64
  twords : ∀ q < 240, s.mem.readW (s.syms Impl.Ed25519.RISCV64.bSym + BitVec.ofNat 64 (8 * q)) 64 =
    Impl.Ed25519.RISCV64.bWord q
  tC : (vtbR s).Disjoint ⟨s.gpr .a4, 8192⟩
  tF : (vtbR s).Disjoint ⟨s.gpr .a5, 272⟩
  tB : (vtbR s).Disjoint (below s.sp 208)
  tal : (s.syms Impl.Ed25519.RISCV64.bSym).toNat % 8 = 0

/-- What the body may write. -/
abbrev verW (s : State) : List Region := [⟨s.gpr .a4, 8192⟩, ⟨s.gpr .a5, 272⟩, below s.sp 208]

/-- The values in `s7`–`s10`. -/
def verV (s : State) : Reg → BitVec 64
  | .s7 => s.gpr .a1 | .s8 => s.gpr .a2 | .s9 => s.gpr .a4 | .s10 => s.gpr .a5 | _ => 0

abbrev VerInv (s : State) : State → Prop := Inv s (s.gpr .a5) 224 verifyRegs (verV s) (verW s)

theorem verifyRegs_pres : ∀ r ∈ verifyRegs, r ∈ preserved := by decide

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
  obtain hs : Region.Sub (slotArea (s.gpr .a5) 224 verifyRegs) ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  refine Inv.step h verifyRegs_pres hrd hwr hsp hg hf (fun r hr => ?_) fun r hr => ?_
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, Offset.sub_base _ (by omega_using [hdn])⟩
  · rcases hW r hr with rfl | rfl | ⟨d, n, hdn, rfl⟩
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs
    · exact Offset.disjoint _ (.inr hdn) (by decide) (by omega_using [hdn])

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
  obtain hF : (⟨s.gpr .a5, 272⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hsl : ∀ p ∈ slots 224 verifyRegs, p.2 + 8 ≤ 272 := by decide
  refine save_ok hp.alF (by decide) (by decide)
    (fun p hp' => in_base hF (hsl p hp') (by have := hsl p hp'; omega_using [this])) fun u hu hsv hfr => ?_
  unfold mov
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => ?_
  obtain m₄ : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  obtain g₄ : ∀ r, r ∉ verifyRegs → u₄.gpr r = u.gpr r := fun r hr => by
    simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d⟩ := hr
    rw [h₄.other _ d, h₃.other _ c, h₂.other _ b, h₁.other _ a]
  obtain gu : ∀ r, u.gpr r = s.gpr r := fun r => hu.gpr r (by simp)
  obtain rd₄ : u₄.rd = s.rd := by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, hu.rd]
  obtain wr₄ : u₄.wr = s.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, hu.wr]
  obtain sp₄ : u₄.sp = s.sp := by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, hu.sp]
  obtain e10 : u₄.gpr .s10 = s.gpr .a5 := by rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide),
    h₁.other _ (by decide), gu]
  obtain hS : (⟨s.gpr .a3, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  obtain hP : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  -- The signature, then `pk`.
  refine copyIn_ok (P := s.gpr .a3) (F := s.gpr .a5) (o := 128) (n := 64) (by decide) (by decide)
    (by rw [g₄ _ (by decide), gu]) e10 (by decide)
    (fun i hi => by rw [rd₄, wr₄]; exact in_base (List.mem_append_left _ hS) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => by rw [wr₄]; exact in_base hF (by omega_using [hi]) (by omega_using [hi]))
    (hp.sF.sub_right (Offset.sub_base _ (by decide))) fun v hv hfv hbv => ?_
  rw [← List.append_nil (copyIn .a0 .s10 192)]
  refine copyIn_ok (P := s.gpr .a0) (F := s.gpr .a5) (o := 192) (n := 32) (by decide) (by decide)
    (by rw [hv.gpr _ (by decide), g₄ _ (by decide), gu]) (by rw [hv.gpr _ (by decide), e10]) (by decide)
    (fun i hi => by rw [hv.rd, hv.wr, rd₄, wr₄]; exact in_base (List.mem_append_left _ hP) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi => by rw [hv.wr, wr₄]; exact in_base hF (by omega_using [hi]) (by omega_using [hi]))
    (hp.pF.sub_right (Offset.sub_base _ (by decide))) fun t ht hft hbt => WP.block_nil ?_
  obtain F128 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 128, 64⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain F192 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain fin : Frame [⟨s.gpr .a5, 272⟩] s.mem t.mem :=
    (hfr.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨⟨s.gpr .a5, 272⟩, by simp, Offset.sub_base _ (by decide)⟩).trans
      ((by rw [m₄] at hfv; exact hfv.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F128⟩ :
        Frame [⟨s.gpr .a5, 272⟩] u.mem v.mem).trans
        (hft.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, F192⟩))
  obtain keepIn : ∀ {p : Addr} {n : Nat}, n < 2 ^ 64 → Region.Disjoint ⟨p, n⟩ ⟨s.gpr .a5, 272⟩ →
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
    obtain e : bytesAt v.mem (s.gpr .a0) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
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
  obtain hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega)
  exact bytes_keep hf (by omega) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.cF.symm.sub_left hs
    · exact hp.bF.symm.sub_left hs

theorem verifyHash_ok (C : ShaOK) {s : State} (hp : VerPre s) : WP isa verifyHash s (VerArgs s) := by
  obtain hlen : (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 := len_add_le (Nat.le_of_lt (s.gpr .a2).isLt) (by decide) hp.mC
  obtain scW : ∀ {t : State}, VerInv s t → ∀ r ∈ [(⟨s.gpr .a4, 8192⟩ : Region), below t.sp 208], VerWr s r :=
    fun h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by rw [h.sp]))
  obtain F0 : Region.Sub ⟨s.gpr .a5, 32⟩ ⟨s.gpr .a5, 272⟩ := Region.sub_prefix (by decide)
  obtain F64 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 64, 64⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain F128 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 128, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain F192 : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by decide)
  obtain inRd : ∀ {t : State}, VerInv s t → ∀ {r : Region}, r ∈ s.rd → Covers [r] (t.rd ++ t.wr) :=
    fun h r hr a n hi => by
      obtain ⟨r', hr', hc⟩ := hi
      rw [List.mem_singleton.mp hr'] at hc
      exact ⟨r, List.mem_append_left _ (by rw [h.rd]; exact hr), hc⟩
  obtain inF : ∀ {t : State}, VerInv s t → ∀ {d n : Nat}, d + n ≤ 272 →
      Covers [⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩] (t.rd ++ t.wr) := fun h d n hdn =>
    Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ (ver_Fw hp h), d, rfl, hdn⟩
  unfold verifyHash
  refine WP.seq (WP.mono (verSetup_ok hp) fun t₁ ⟨h₁, cs₁, cp₁⟩ => ?_)
  refine WP.seq (hashInit_ok C (sr := .s9) (h₁.regs _ (by decide)) (ver_env hp h₁)
    fun t₂ a b c f₂ g hr₂ => ?_)
  obtain h₂ := verStep hp h₁ a b c g f₂ (scW h₁)
  obtain cs₂ : bytesAt t₂.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₁.sp f₂ (by decide) (by decide), cs₁]
  obtain cp₂ : bytesAt t₂.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₁.sp f₂ (by decide) (by decide), cp₁]
  -- `R`, the signature's first half, from its copy.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s10) (off := 128) (len := 32) (by decide)
    (by decide) (by decide) (h₂.regs _ (by decide)) (by rw [h₂.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 0) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₂) (inF h₂ (by decide))
    (hp.cF.symm.sub_left F128) (by rw [h₂.sp]; exact hp.bF.sub_right F128) fun t₃ a b c f₃ g hr₃ => ?_)
  obtain h₃ := verStep hp h₂ a b c g f₃ (scW h₂)
  obtain r₃ : Repr t₃.mem (s.gpr .a4) (bytesAt s.mem (s.gpr .a3) 32) := by
    have := hr₃ [] hr₂ rfl
    rwa [List.nil_append, ← Proof.Ed25519.signatureBytes_take, cs₂, Proof.Ed25519.signatureBytes_take] at this
  obtain cp₃ : bytesAt t₃.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₂.sp f₃ (by decide) (by decide), cp₂]
  obtain cs₃ : bytesAt t₃.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₂.sp f₃ (by decide) (by decide), cs₂]
  -- `A`, from its copy.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s10) (off := 192) (len := 32) (by decide)
    (by decide) (by decide) (h₃.regs _ (by decide)) (by rw [h₃.regs _ (by decide)]; rfl)
    (Sets.li (d := .a1) (k := 32) (by decide)) (Sets.li (d := .a3) (k := 32) (by decide))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl (ver_env hp h₃) (inF h₃ (by decide))
    (hp.cF.symm.sub_left F192) (by rw [h₃.sp]; exact hp.bF.sub_right F192) fun t₄ a b c f₄ g hr₄ => ?_)
  obtain h₄ := verStep hp h₃ a b c g f₄ (scW h₃)
  obtain r₄ : Repr t₄.mem (s.gpr .a4) (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32) := by
    have := hr₄ _ r₃ (by simp [bytesAt])
    rwa [cp₃] at this
  obtain cs₄ : bytesAt t₄.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₃.sp f₄ (by decide) (by decide), cs₃]
  obtain cp₄ : bytesAt t₄.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
    rw [copies_keep hp h₃.sp f₄ (by decide) (by decide), cp₃]
  -- The message.
  refine WP.seq (hashUpdate_ok C (sr := .s9) (src := .s7) (off := 0) (len := (s.gpr .a2).toNat) (by decide)
    (by decide) (by decide) (h₄.regs _ (by decide))
    (by rw [h₄.regs _ (by decide), BitVec.add_zero]; rfl)
    (Sets.li (d := .a1) (k := 64) (by decide)) (Sets.mov (d := .a3) (n := .s8))
    (fun _ _ _ => rfl) (fun g g' hg => by rw [hg .s8 (by decide) (by decide) (by decide)])
    (by rw [h₄.regs _ (by decide)]; rfl) (ver_env hp h₄) (inRd h₄ (by rw [hp.rd]; simp))
    hp.mC (by rw [h₄.sp]; exact hp.bM) fun t₅ a b c f₅ g hr₅ => ?_)
  obtain h₅ := verStep hp h₄ a b c g f₅ (scW h₄)
  obtain r₅ : Repr t₅.mem (s.gpr .a4)
      (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s) := by
    have := hr₅ _ r₄ (by simp [bytesAt])
    rwa [ver_input h₄ (s.gpr .a2).isLt hp.mC hp.mF hp.bM.symm] at this
  obtain cs₅ : bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 128) 64 = bytesAt s.mem (s.gpr .a3) 64 := by
    rw [copies_keep hp h₄.sp f₅ (by decide) (by decide), cs₄]
  obtain cp₅ : bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a0) 32 := by
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
  obtain h₆ := verStep hp h₅ a b c g f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨64, 64, by decide, rfl⟩)
    · exact .inr (.inl (by rw [h₅.sp])))
  obtain dg : bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 64) 64 =
      Spec.Sha512.sha512 (bytesAt s.mem (s.gpr .a3) 32 ++ bytesAt s.mem (s.gpr .a0) 32 ++ vmsgB s) :=
    hd₆ _ r₅ (by simp [bytesAt]; omega_using [hlen])
      (by rw [h₅.regs _ (by decide), cnt_eq, verV_s8]; simp [bytesAt]; congr 1; omega_using [])
  obtain keep6 : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₅.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun {d n} hd hdn => bytes_keep f₆ (by omega_using [hdn]) fun r hr => by
      obtain hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega_using [hdn])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact Offset.disjoint _ (.inr (by omega_using [hd])) (by omega_using [hdn]) (by omega_using [])
      · rw [h₅.sp]; exact hp.bF.symm.sub_left hs
  obtain cs₆ := (keep6 (d := 128) (n := 64) (by decide) (by decide)).trans cs₅
  obtain cp₆ := (keep6 (d := 192) (n := 32) (by decide) (by decide)).trans cp₅
  -- `scalar_reduce`.
  obtain ce : ∀ (u : State) q, q ∉ linkRegs → ∀ rd wr, (u.callEntry.withRegions rd wr).gpr q = u.gpr q :=
    fun _ q hq _ _ => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  obtain hFw := ver_Fw hp h₆
  obtain hCw : (⟨s.gpr .a4, 8192⟩ : Region) ∈ t₆.wr := (ver_env hp h₆).w
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
  obtain h₈ := verStep hp h₆ (a.trans k₇.rd) (b.trans k₇.wr) (c.trans k₇.sp)
    (fun r hr => (g r hr).trans (k₇.pres r hr)) (k₇.mem ▸ f₈) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr ⟨0, 32, by decide, by simp⟩)
      · exact .inl rfl
  obtain keep8 : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt t₈.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₆.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun {d n} hd hdn => by
      rw [← k₇.mem]
      exact bytes_keep f₈ (by omega_using [hdn]) fun r hr => by
        obtain hs : Region.Sub ⟨s.gpr .a5 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .a5, 272⟩ := Offset.sub_base _ (by omega_using [hdn])
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hdn])
        · exact hp.cF.symm.sub_left hs
  obtain cs₈ := (keep8 (d := 128) (n := 64) (by decide) (by decide)).trans cs₆
  obtain cp₈ := (keep8 (d := 192) (n := 32) (by decide) (by decide)).trans cp₆
  -- The upper half zeroed, and the arguments.
  obtain hFw₈ : (⟨s.gpr .a5, 272⟩ : Region) ∈ t₈.wr := ver_Fw hp h₈
  obtain e10 : t₈.gpr .s10 = s.gpr .a5 := h₈.regs _ (by decide)
  obtain inF8 : ∀ (u : State), u.wr = t₈.wr → ∀ d, d + 8 ≤ 272 → InRegions u.wr (s.gpr .a5 + BitVec.ofNat 64 d) 8 :=
    fun u hu d hd => by rw [hu]; exact in_base hFw₈ hd (by omega_using [hd])
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
  obtain z₂ : u₂.gpr .a5 = 0 := by rw [e₂.gpr, z₁]
  obtain z₃ : u₃.gpr .a5 = 0 := by rw [e₃.gpr, z₂]
  obtain z₄ : u₄.gpr .a5 = 0 := by rw [e₄.gpr, z₃]
  obtain mv : v₄.mem = ((((t₈.mem.writeW (s.gpr .a5 + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW
      (s.gpr .a5 + BitVec.ofNat 64 40) (0 : BitVec 64)).writeW (s.gpr .a5 + BitVec.ofNat 64 48) (0 : BitVec 64)).writeW
      (s.gpr .a5 + BitVec.ofNat 64 56) (0 : BitVec 64)) := by
    rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem, e₅.mem, e₄.mem, e₃.mem, e₂.mem, e₁.mem, z₁, z₂, z₃, z₄]
  obtain gp : ∀ r ∈ preserved, v₄.gpr r = t₈.gpr r := fun r hr => by
    obtain ⟨p0, p1, p2, p3, -⟩ := pres_args hr
    rw [g₄.other _ p3, g₃.other _ p2, g₂.other _ p1, g₁.other _ p0, e₅.gpr, e₄.gpr, e₃.gpr, e₂.gpr,
      e₁.other _ (by revert hr; cases r <;> decide)]
  obtain cont : ∀ d, 32 ≤ d → d + 8 ≤ 64 → Region.Contains ⟨s.gpr .a5 + BitVec.ofNat 64 32, 32⟩
      (s.gpr .a5 + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])
  obtain fv : Frame [⟨s.gpr .a5 + BitVec.ofNat 64 32, 32⟩] t₈.mem v₄.mem := by
    rw [mv]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cont 32 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cont 40 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cont 48 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cont 56 (by decide) (by decide))
  obtain rr : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i + 8 ≤ j ∨ j + 8 ≤ i → i + 8 ≤ 272 → j + 8 ≤ 272 →
      (x.writeW (s.gpr .a5 + BitVec.ofNat 64 j) v).readW (s.gpr .a5 + BitVec.ofNat 64 i) 64 =
        x.readW (s.gpr .a5 + BitVec.ofNat 64 i) 64 :=
    fun x i j v h hi hj => Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hi]) (by omega_using [hj])) (by decide)
  obtain hz : ∀ k < 4, v₄.mem.readW (s.gpr .a5 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * k)) 64 = 0 := by
    intro k hk
    rw [mv, Offset.add_add]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl
    · rw [show 32 + 8 * 0 = 32 from rfl, rr _ 32 56 _ (by decide) (by decide) (by decide),
        rr _ 32 48 _ (by decide) (by decide) (by decide), rr _ 32 40 _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 1 = 40 from rfl, rr _ 40 56 _ (by decide) (by decide) (by decide),
        rr _ 40 48 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 2 = 48 from rfl, rr _ 48 56 _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    · rw [show 32 + 8 * 3 = 56 from rfl, Mem.readW_writeW_self64]
  obtain keepv : ∀ {d n : Nat}, 128 ≤ d → d + n ≤ 224 →
      bytesAt v₄.mem (s.gpr .a5 + BitVec.ofNat 64 d) n = bytesAt t₈.mem (s.gpr .a5 + BitVec.ofNat 64 d) n :=
    fun hd hdn => bytes_keep fv (by omega_using [hdn]) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_using [hd])) (by omega_using [hdn]) (by omega_using [])
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

end

end

/-! ### `Ed25519.RISCV64.VerifyVerified`, which only this module used -/

section

/-!
# `vg_ed25519_verify_equation` on RISC-V, by register

The function meets a contract of its facts by register (`verifyRV`), with no
stack, from a working space aligned to 8 bytes, as an `[u64]` is, and the
static of the cached `-[1]B … -[15]B` (`bSym`, `bWord`): the callers in this
library call it through it. It saves and restores the callee-saved registers
and `ra` (`verify_ok'`), given the windows' proof (`RhsOk`). The contract
declares the inputs and the static's address public, and two runs on the
same inputs leak the same trace (`verifyEquation_rel`, `verify_ct`), given
the windows' constant time (`RhsCT`). What a caller's contract under
`abi.withConsts bConsts` says of the static: `bstat_of_consts`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64

/-- `vg_ed25519_verify_equation`'s contract by register, an internal function's. -/
def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 32⟩
    let sig : Region := ⟨s.gpr .a1, 64⟩
    let ch : Region := ⟨s.gpr .a2, 64⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    let tb : Region := ⟨s.syms bSym, 1920⟩
    s.rd = [pk, sig, ch, tb] ∧ s.wr = [ws] ∧ (s.gpr .a3).toNat % 8 = 0 ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧
      ch.Disjoint ws ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧ tb.Disjoint ws ∧
      (s.syms bSym).toNat % 8 = 0
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .a0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a0) 32 ++ Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a1) 64 ++
      Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a2) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a0) 32 ++ Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a1) 64 ++
      Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a2) 64).map (·.toNat) ∧ s₁.syms bSym = s₂.syms bSym

theorem verifyRV_pre {s : State} (hs : verifyRV.pre s) : VerifyPre s :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, h7, h8, h9, h10⟩⟩

theorem verify_ok' (hR : RhsOk) (s : State) (hs : verifyRV.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧
      verifyRV.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hra, hr⟩ := verify_ok hR (verifyRV_pre hs)
  refine ⟨t, s', he, ⟨hg, hsp, hra⟩, ?_⟩
  show (s'.gpr .a0).setWidth 32 = _
  rw [hr]
  split <;> rfl

theorem bytes_of_leak {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  obtain e : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂ := by
    have := congrArg (List.map fun n => BitVec.ofNat 8 n) h
    simpa [List.map_map, Function.comp_def] using this
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verify_ct (hR : RhsOk) (hRC : RhsCT) :
    ConstantTime isa verifyRV.pre verifyRV.pub Impl.Ed25519.RISCV64.verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨p0, p1, p2, p3, psp, pl, psy⟩ := hp
  obtain hl : ∀ (s : State) (p : Addr) (n : Nat), (Spec.Ed25519.bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [Spec.Ed25519.bytesAt]
  obtain ⟨b0, b1, b2⟩ := bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl]) pl
  refine verifyEquation_rel hR hRC (b := s₁.gpr .a3) (sp := s₁.sp) (pk := s₁.gpr .a0) (sig := s₁.gpr .a1)
    (ch := s₁.gpr .a2) (T := s₁.syms bSym) (PK := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a0) 32)
    (SG := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a1) 64) (CH := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a2) 64)
    _ _ _ _ _ _ ⟨⟨verifyRV_pre h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨verifyRV_pre h₂, psy.symm, p0.symm, p1.symm, p2.symm, p3.symm, psp.symm, by rw [b0, p0], by rw [b1, p1],
        by rw [b2, p2]⟩⟩ e₁ e₂

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {q : Nat} (hq : q < 240) : bWords.getD q 0 = bWord q := by
  simp [bWords, hq]

/-- What `abi.withConsts [(bSym, ws)]` says of the static, for words `ws` of `bWord`. -/
theorem bstat_of_consts' {st : Nat} {s : State} {ws : List (BitVec 64)} (hl : ws.length = 240)
    (hg : ∀ q < 240, ws.getD q 0 = bWord q) (h : ConstsOk [(bSym, ws)] st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat % 8 = 0 ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ RISCV64.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r := by
  have hrd := h.rd1
  obtain hfit := h.fit List.mem_cons_self
  obtain hal := h.aligned List.mem_cons_self
  obtain hd : (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r) ∧
      ∀ r ∈ RISCV64.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r :=
    (h.2.2.1 _ List.mem_cons_self).2
  rw [hl] at hrd hfit hd
  refine ⟨hrd, by omega_using [hal], hfit, fun q hq => ?_, hd.1, hd.2⟩
  rw [h.held1 q (by rw [hl]; exact hq), hg q hq]

/-- What `abi.withConsts bConsts` says of the static. -/
theorem bstat_of_consts {st : Nat} {s : State} (h : ConstsOk bConsts st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat % 8 = 0 ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ RISCV64.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r :=
  bstat_of_consts' bWords_length (fun _ hq => bWords_getD hq) h

/-- The readable regions under `abi.withConsts bConsts`: those without it, then the static. -/
theorem rd_of_bconsts' {st : Nat} {s : State} {ws : List (BitVec 64)} {L : List Region}
    (hl : ws.length = 240) (h : ConstsOk [(bSym, ws)] st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] := by
  have h1 := h.1
  simp only [List.length_singleton, constRegs, Abi.constRegions, List.map_cons, List.map_nil, hl] at h1
  calc s.rd = s.rd.take (s.rd.length - 1) ++ s.rd.drop (s.rd.length - 1) := (List.take_append_drop _ _).symm
    _ = L ++ [⟨s.syms bSym, 1920⟩] := by rw [hL, h1]

theorem rd_of_bconsts {st : Nat} {s : State} {L : List Region} (h : ConstsOk bConsts st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] :=
  rd_of_bconsts' bWords_length h hL

end VG.Proof.Ed25519.RISCV64

end

end


/-!
# `vg_ed25519_verify` on RISC-V, with its frame as an argument

The challenge (`verifyHash_ok`), the call of `vg_ed25519_verify_equation` on
the copies of `pk` and the signature (`verCall_ok`) and the restores: `a0`
then holds `verify`'s result (`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

/-- `verify`'s result on the inputs on entry. -/
abbrev verResult (s : State) : BitVec 32 :=
  if Spec.Ed25519.verify (bytesAt s.mem (s.gpr .a0) 32) (vmsgB s) (bytesAt s.mem (s.gpr .a3) 64) then 1 else 0

/-- The inputs of `verify_equation`: the copies of `pk` and the signature, and the challenge, in `F`. -/
abbrev verRd (s : State) : List Region :=
  [⟨s.gpr .a5 + BitVec.ofNat 64 192, 32⟩, ⟨s.gpr .a5 + BitVec.ofNat 64 128, 64⟩, ⟨s.gpr .a5, 64⟩, vtbR s]

/-- The narrowed state `verify_equation` starts in. -/
theorem verCall_pre {s t : State} (hp : VerPre s) (ha : VerArgs s t) (sy : t.syms = s.syms) :
    verifyRV.pre (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]) := by
  obtain ce : ∀ q, q ∉ linkRegs → (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).gpr q = t.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have cy : (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).syms = s.syms := sy
  obtain cm : (t.callEntry.withRegions (verRd s) [⟨s.gpr .a4, 8192⟩]).mem = t.mem := by
    rw [State.withRegions_mem, State.callEntry_mem]
  refine ⟨by rw [State.withRegions_rd, ce _ (by decide), ce _ (by decide), ce _ (by decide), ha.a0, ha.a1, ha.a2, cy],
    by rw [State.withRegions_wr, ce _ (by decide), ha.a3], by rw [ce _ (by decide), ha.a3]; exact hp.alC,
    by rw [ce _ (by decide), ce _ (by decide), ha.a0, ha.a3]; exact hp.cF.symm.sub_left (Offset.sub_base _ (by decide)),
    by rw [ce _ (by decide), ce _ (by decide), ha.a1, ha.a3]; exact hp.cF.symm.sub_left (Offset.sub_base _ (by decide)),
    by rw [ce _ (by decide), ce _ (by decide), ha.a2, ha.a3]; exact hp.cF.symm.sub_left (Region.sub_prefix (by decide)),
    by rw [cy]; exact hp.tfit, fun q hq => ?_, by rw [cy, ce _ (by decide), ha.a3]; exact hp.tC,
    by rw [cy]; exact hp.tal⟩
  rw [cy, cm, ← hp.twords q hq]
  refine ha.inv.frame.readW (r := vtbR s) (Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])) (fun r hr => ?_) (by decide)
  simp only [verW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.tC
  · exact hp.tF
  · exact hp.tB

theorem verCall_covers {s t : State} (hp : VerPre s) (ha : VerArgs s t) :
    Covers (verRd s ++ [⟨s.gpr .a4, 8192⟩]) (t.rd ++ t.wr) ∧ Covers [⟨s.gpr .a4, 8192⟩] t.wr := by
  rw [ha.inv.rd, ha.inv.wr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 192, rfl, show 192 + 32 ≤ 272 by decide⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 128, rfl, show 128 + 64 ≤ 272 by decide⟩
    · exact ⟨⟨s.gpr .a5, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨vtbR s, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨s.gpr .a4, 8192⟩, by simp, 0, by simp, by simp⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨⟨s.gpr .a4, 8192⟩, by simp, 0, by simp, by simp⟩

theorem verifyEquation_noFrames : Impl.Ed25519.RISCV64.verifyEquation.noFrames = true := by decide +kernel

/-- The call of `verify_equation`. -/
theorem verCall_ok (hR : RhsOk) {s t : State} (hp : VerPre s) (ha : VerArgs s t) (sy : t.syms = s.syms) :
    WP isa (.call "vg_ed25519_verify_equation" Impl.Ed25519.RISCV64.verifyEquation) t fun t' =>
      VerInv s t' ∧ (t'.gpr .a0).setWidth 32 = verResult s := by
  obtain ⟨hc, hw⟩ := verCall_covers hp ha
  refine WP.call (k := verifyRV) (verify_ok' hR) (verCall_pre hp ha sy) hc hw (fun t' a b c f g _ hpost => ?_)
    verifyEquation_noFrames
  have hp' : (t'.gpr .a0).setWidth 32 = if Spec.Ed25519.verifyEquation (bytesAt t.mem (t.gpr .a0) 32)
      (bytesAt t.mem (t.gpr .a1) 64) (bytesAt t.mem (t.gpr .a2) 64) then 1 else 0 := hpost
  rw [ha.a0, ha.a1, ha.a2, ha.ch, ha.pk, ha.sig] at hp'
  refine ⟨verStep hp ha.inv a b c g f fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl rfl, hp'.trans ?_⟩
  unfold verResult Spec.Ed25519.verify
  rw [Proof.Ed25519.signatureBytes_take]

theorem verifyMessage_wp (C : ShaOK) (hR : RhsOk) {s : State} (hp : VerPre s) :
    WP isa verifyMessage s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ (t.gpr .a0).setWidth 32 = verResult s := by
  unfold verifyMessage
  refine WP.seq (WP.mono_syms (verifyHash_ok C hp) fun t ha sy => ?_)
  refine WP.seq (WP.mono (verCall_ok hR hp ha sy) fun t' ⟨h', hr⟩ => ?_)
  obtain hFw : (⟨s.gpr .a5, 272⟩ : Region) ∈ t'.rd ++ t'.wr := List.mem_append_right _ (ver_Fw hp h')
  obtain hrl : ∀ p ∈ restoreList 224 verifyRegs, p.2 + 8 ≤ 272 := by decide
  refine restore_ok h' hp.alF (h'.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega_using [this]))
    fun t₅ g₅ sp₅ ra₅ _ o₅ => ⟨g₅, sp₅, ra₅, ?_⟩
  rw [o₅ _ (by decide) (by decide), hr]

end VG.Proof.Ed25519.RISCV64.Whole

end

end

/-!
# `vg_ed25519_verify` on RISC-V, with its frame as an argument: by register, and constant time

The contract by register (`verC`), from an aligned `scratch`, and the
proof against it (`ver_ok`). The contract declares the inputs public, and
two runs on the same inputs leak the same trace (`ver_ct`): the taint
analysis checks the challenge's computation (only the pointers and the
length are public to it, and they stay in `s7`–`s10`), and the call of
`verify_equation`, whose branches depend on the inputs, is related by its
own constant time and the arguments' agreement (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (bSym bConsts)
open VG.Proof.Ed25519.RISCV64 (bstat_of_consts rd_of_bconsts RhsOk RhsCT)

/-- The contract by register: `pk` in `a0`, the message in `a1` (`len` in `a2`), the signature in
`a3`, `scratch` in `a4`, the frame in `a5`; without the static. -/
def verR : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 32⟩
    let msg : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let sig : Region := ⟨s.gpr .a3, 64⟩
    let sc : Region := ⟨s.gpr .a4, 8192⟩
    let fr : Region := ⟨s.gpr .a5, 272⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [sc, fr] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ (s.gpr .a5).toNat % 8 = 0 ∧
      pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧ msg.Disjoint fr ∧ sig.Disjoint sc ∧ sig.Disjoint fr ∧
      sc.Disjoint fr ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint pk ∧ (below s.sp 208).Disjoint msg ∧ (below s.sp 208).Disjoint sig ∧
      (below s.sp 208).Disjoint sc ∧ (below s.sp 208).Disjoint fr
  post s s' := (s'.gpr .a0).setWidth 32 = verResult s
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp ∧
    (bytesAt s₁.mem (s₁.gpr .a0) 32 ++ bytesAt s₁.mem (s₁.gpr .a1) (s₁.gpr .a2).toNat ++
      bytesAt s₁.mem (s₁.gpr .a3) 64).map (·.toNat) =
    (bytesAt s₂.mem (s₂.gpr .a0) 32 ++ bytesAt s₂.mem (s₂.gpr .a1) (s₂.gpr .a2).toNat ++
      bytesAt s₂.mem (s₂.gpr .a3) 64).map (·.toNat)

/-- `verR` with the static of `verify_equation` (`abi.withConsts bConsts`). -/
def verC : Contract isa where
  pre s := verR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts 208 s
  post := verR.post
  pub s₁ s₂ := verR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s := by
  obtain ⟨⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r⟩, hk⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := bstat_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a0, 32⟩, vmsgR s, ⟨s.gpr .a3, 64⟩, vtbR s] := rd_of_bconsts hk a
  have hB : below s.sp 208 ∈ RISCV64.abi.reserved 208 s := by
    show _ ∈ stackBelow s.sp 208
    rw [stackBelow_pos _ (by decide)]; simp
  exact ⟨hrd, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r, tfit, words, twr _ (by rw [b]; simp),
    twr _ (by rw [b]; simp), tres _ hB, tal⟩

theorem ver_ok (hR : RhsOk) (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := verifyMessage_wp sha512OK hR (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

/-- Two runs on the same public data, as `RelCT.constantTime` relates them. -/
abbrev VP (s₁ s₂ : State) : Prop := verC.pre s₁ ∧ verC.pre s₂ ∧ verC.pub s₁ s₂

/-- The inputs agree in two such runs. -/
theorem vp_bytes {s₁ s₂ : State} (h : VP s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .a0) 32 = bytesAt s₂.mem (s₂.gpr .a0) 32 ∧ vmsgB s₁ = vmsgB s₂ ∧
      bytesAt s₁.mem (s₁.gpr .a3) 64 = bytesAt s₂.mem (s₂.gpr .a3) 64 := by
  obtain ⟨-, -, ⟨-, -, p2, -, -, -, -, pl⟩, -⟩ := h
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [bytesAt]
  exact bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl, p2]) pl

/-- The restores, with `F` in `s10` in both runs. -/
theorem restore_ct {P : State → State → Prop}
    (hp : ∀ t₁ t₂, P t₁ t₂ → t₁.sp = t₂.sp ∧ t₁.gpr .s10 = t₂.gpr .s10) :
    RelCT isa P (.block (restoreRegs .s10 224 verifyRegs)) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.s10]) (fun t₁ t₂ h => ⟨(hp _ _ h).1, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr; exact (hp _ _ h).2⟩) (by taint_decide)

/-- Two runs' entry states. -/
abbrev VPair : Type := {σ : State × State // VP σ.1 σ.2}

theorem ver_ct (hR : RhsOk) (hRC : RhsCT) : ConstantTime isa verC.pre verC.pub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold verifyMessage
  refine RelCT.seq (R := fun (t₁ t₂ : State) => ∃ σ : VPair, (VerArgs σ.1.1 t₁ ∧ t₁.syms = σ.1.1.syms) ∧
    (VerArgs σ.1.2 t₂ ∧ t₂.syms = σ.1.2.syms)) ?_ <|
    RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerInv σ.1.1 t₁ ∧ VerInv σ.1.2 t₂) ?_ ?_
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (fun s₁ s₂ h => ?_)
      (by taint_decide)).wpDep (F := fun (s t : State) => VerArgs s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨⟨(σ₁, σ₂), hp⟩, a₁, a₂⟩
    obtain ⟨-, -, ⟨p0, p1, p2, p3, p4, p5, psp, -⟩, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ => ?_
    refine ((RelCT.callEx (k := verifyRV) (verify_ok' hR) (verify_ct hR hRC)
      fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ => ?_).wp
      (F₁ := VerInv σ.1.1) (F₂ := VerInv σ.1.2) fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ =>
        ⟨WP.mono (verCall_ok hR (verC_pre σ.2.1) a₁ y₁) fun _ h => h.1,
          WP.mono (verCall_ok hR (verC_pre σ.2.2.1) a₂ y₂) fun _ h => h.1⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, i₁, i₂⟩ => ⟨σ, i₁, i₂⟩
    have hp₁ := verC_pre σ.2.1
    have hp₂ := verC_pre σ.2.2.1
    obtain ⟨c₁, w₁⟩ := verCall_covers hp₁ a₁
    obtain ⟨c₂, w₂⟩ := verCall_covers hp₂ a₂
    refine ⟨_, _, _, _, verCall_pre hp₁ a₁ y₁, verCall_pre hp₂ a₂ y₂, ?_, c₁, w₁, c₂, w₂⟩
    obtain ⟨-, -, ⟨p0, p1, p2, p3, p4, p5, psp, -⟩, psy⟩ := σ.2
    obtain ⟨b0, bm, b3⟩ := vp_bytes σ.2
    have ch : vChallenge σ.1.1 = vChallenge σ.1.2 := by
      unfold vChallenge
      rw [← Proof.Ed25519.signatureBytes_take, ← Proof.Ed25519.signatureBytes_take σ.1.2.mem, b3, b0, bm]
    simp only [verifyRV, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
    rw [a₁.a0, a₂.a0, a₁.a1, a₂.a1, a₁.a2, a₂.a2, a₁.a3, a₂.a3, a₁.inv.sp, a₂.inv.sp, a₁.ch, a₂.ch,
      a₁.pk, a₂.pk, a₁.sig, a₂.sig, b0, b3, ch]
    exact ⟨by rw [p5], by rw [p5], p5, p4, psp, rfl, by
      show t₁.syms bSym = t₂.syms bSym
      rw [y₁, y₂]; exact psy⟩
  · exact RelCT.exists_ fun σ => restore_ct fun t₁ t₂ ⟨i₁, i₂⟩ => by
      obtain ⟨-, -, ⟨-, -, -, -, -, p5, psp, -⟩, -⟩ := σ.2
      exact ⟨by rw [i₁.sp, i₂.sp]; exact psp, by
        rw [i₁.regs .s10 (by decide), i₂.regs .s10 (by decide), verV_s10, verV_s10]
        exact p5⟩

end VG.Proof.Ed25519.RISCV64.Whole
