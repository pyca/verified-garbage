import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecPriv
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: after the private-key operation

From the call of the private-key operation to the output, the function
writes only the first `scrBytes` bytes of `scratch`, its slots from `oI` on
and the stack below its frame (`Safe`): through all of it, `Ctx`, the result
`R` in its slot and `EM` in `out` stay as they are (`Post`, `Post.step`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (bytesAt_eq)

/-- The part of `scratch` used after the private-key operation. -/
def scrBytes : Nat := 3440

/-- That part. -/
abbrev Lay.SC (L : Lay) : Region := ⟨L.scr, scrBytes⟩

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

theorem Lay.Ok.sc_sub {L : Lay} (hL : L.Ok) : Region.Sub L.SC L.SCR :=
  Region.sub_prefix (by have := hL.s8192; unfold scrBytes; omega)

/-- What a step after the private-key operation may write. -/
def Safe (L : Lay) (r : Region) : Prop :=
  Region.Sub r L.SC ∨ Region.Sub r L.LOW ∨
    ∃ d, oI ≤ d ∧ d + r.len ≤ frameBytes ∧ r.base = L.Q + BitVec.ofNat 64 d

/-- After the private-key operation: `Ctx`, its result `R` in its slot and
`EM` in `out`. -/
structure Post (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  r : t.mem.readW (L.Q + BitVec.ofNat 64 oR) 64 = R
  em : Spec.Rsa.bytesAt t.mem L.out L.k.toNat = EM

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}
  {t t' : State}

/-- A step that writes only where it may keeps `Post`. -/
theorem Post.step (hL : L.Ok) (hc : Post L g vv m₀ R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) {ws : List Region} (hf : Frame ws t.mem t'.mem)
    (hs : ∀ r ∈ ws, Safe L r) : Post L g vv m₀ R EM t' := by
  have hnQ := hL.nQ
  have hb := hL.bO
  have hcx := hc.ctx
  refine ⟨⟨hrd.trans hcx.rd, hwr.trans hcx.wr, hsp.trans hcx.sp, fun r hr hr' => (hg r hr hr').trans (hcx.cs r hr hr'),
    fun r hr => (hv r hr).trans (hcx.vs r hr), hcx.kept.frame hf fun d hd X hX => ?_,
    hcx.frame.trans (hf.sub fun r hr => ?_)⟩, ?_, ?_⟩
  · rcases hs X hX with h | h | ⟨d', h₁, h₂, hb⟩
    · exact hL.kept_buf hd (.inr (.inr (sub_trans h hL.sc_sub)))
    · exact (hL.fr_low (by unfold keptOff at hd; omega)).sub_right h
    · obtain ⟨b, n⟩ := X
      simp only at hb h₂; subst hb
      unfold keptOff at hd; unfold oI at h₁; unfold frameBytes at h₂
      exact hL.fr_sep (by omega) (by omega) (by omega)
  · rcases hs r hr with h | h | ⟨d', h₁, h₂, hb⟩
    · exact ⟨L.SCR, by simp, sub_trans h hL.sc_sub⟩
    · exact ⟨L.STK, by simp, sub_trans h Lay.Ok.low_stk⟩
    · obtain ⟨b, n⟩ := r
      simp only at hb h₂; subst hb
      unfold frameBytes at h₂
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega)⟩
  · rw [hf.readW (Region.contains_self _ _) (fun X hX => ?_) (by decide)]
    · exact hc.r
    · rcases hs X hX with h | h | ⟨d', h₁, h₂, hb⟩
      · exact hL.stk_buf (by decide) (.inr (.inr (sub_trans h hL.sc_sub)))
      · exact (hL.fr_low (by decide)).sub_right h
      · obtain ⟨b, n⟩ := X
        simp only at hb h₂; subst hb
        unfold oI at h₁; unfold frameBytes at h₂
        exact hL.fr_sep (by unfold oR; omega) (by decide) (by omega)
  · rw [← hc.em]
    refine bytesAt_eq fun i hi => hf.bytes (R := L.OUT) (fun X hX => ?_) (by show L.k.toNat ≤ 2 ^ 64; omega) hi
    rcases hs X hX with h | h | ⟨d', h₁, h₂, hb⟩
    · exact hL.oS.sub_right (sub_trans h hL.sc_sub)
    · exact hL.kO.symm.sub_right (sub_trans h Lay.Ok.low_stk)
    · obtain ⟨b, n⟩ := X
      simp only at hb h₂; subst hb
      unfold frameBytes at h₂
      exact (hL.kO.sub_left (Lay.Ok.sub_stk (by omega))).symm

/-- Code that changes only registers but the callee-saved ones keeps `Post`. -/
theorem Post.regs (hc : Post L g vv m₀ R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) :
    Post L g vv m₀ R EM t' :=
  ⟨hc.ctx.regs hrd hwr hsp hm hv hg, by rw [hm]; exact hc.r, by rw [hm]; exact hc.em⟩

/-- What a call leaves, for writes in `scratch` (and the 16 bytes below the frame). -/
theorem Post.after (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : Proof.Pbkdf2.Md.AArch64.Calls.After t ws t') (hs : ∀ r ∈ ws, Region.Sub r L.SC) :
    Post L g vv m₀ R EM t' :=
  hc.step hL h.rd h.wr h.sp h.vec h.cs h.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (hs r hr)
    · rw [List.mem_singleton.mp hr, hc.ctx.sp]
      exact .inr (.inl (Offset.sub_below _ hP (by have := hL.pQ; omega)))

end

/-! ## Ranges of `scratch` -/

section
variable {L : Lay}

/-- `scratch + a`. -/
abbrev scA (L : Lay) (a : Nat) : Addr := L.scr + BitVec.ofNat 64 a

theorem scD (hL : L.Ok) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ scrBytes) (hb : b + m ≤ scrBytes) :
    Region.Disjoint ⟨scA L a, n⟩ ⟨scA L b, m⟩ :=
  Offset.disjoint L.scr h (by have := hL.bS; have := hL.s8192; unfold scrBytes at ha; omega)
    (by have := hL.bS; have := hL.s8192; unfold scrBytes at hb; omega)

theorem scSub {a n : Nat} (ha : a + n ≤ scrBytes) : Region.Sub ⟨scA L a, n⟩ L.SC :=
  Offset.sub_base _ ha

/-- The 16 bytes below the frame miss `scratch`. -/
theorem stkD (hL : L.Ok) (hP : 16 ≤ L.P) {a m : Nat} (ha : a + m ≤ scrBytes) :
    (below L.Q 16).Disjoint ⟨scA L a, m⟩ :=
  (hL.kS.sub_left (sub_trans (Offset.sub_below _ hP (by have := hL.pQ; omega)) Lay.Ok.low_stk)).sub_right
    (sub_trans (scSub ha) hL.sc_sub)

theorem scCov (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {a n : Nat} (ha : a + n ≤ scrBytes) : Covers [⟨scA L a, n⟩] t.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨L.SCR, by rw [hc.wr]; simp, a, rfl, by
      have := hL.s8192; unfold scrBytes at ha; dsimp only; omega⟩

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
