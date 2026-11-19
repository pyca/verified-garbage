module

public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTOne
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTOne
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCryptFn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Flush
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Rsa.ZeroTest32
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCrypt
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn

/-! ### `Sm4Gcm.Arm.CTStream`, which only this module used -/

section

/-! ### `Sm4Gcm.Arm.StreamInit`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_init`

Untrusted: everything here is checked by Lean. `stream_init` saves our
caller's registers in `scratch` (`W`) and writes the state's `J₀`, its zero
accumulator and its first counter block with `j0` (`streamInit_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr)
open VG.Spec.Gcm (ctxH)

/-- The layout of `stream_init`. -/
theorem siLay {s₀ : State} (h : streamInitArm.pre s₀) :
    Lay (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, -, -, dsW, -, -, bc, -, bs, bW, fc, -, fs, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SI1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r1
  r5 : s₁.gpr .r5 = s₀.gpr .r2
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : SavedAt s₁.mem (arg s₀ 0) s₀
  frame : Frame [savedR (arg s₀ 0)] s₀.mem s₁.mem

theorem si1_wp {s₀ : State} (h : streamInitArm.pre s₀) : WP isa (.block streamInitPre) s₀ (SI1 s₀) := by
  have hp := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fW, -, spf⟩ := hp
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r3), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 0), 768⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha := arg_in (s := s₀) (n := 1) (i := 0) (by decide) spf (by rw [hrd]; simp)
  refine entry_ok (off := 0) (by decide) ha fW hW fun s₁ g12 g rd wr sp sv fr => WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12, stackArg_zero]
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact rd
  · exact wr

theorem si_j0In {s₀ s₁ : State} (h : streamInitArm.pre s₀) (h1 : SI1 s₀ s₁) :
    J0In (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (s₀.gpr .r1) (s₀.gpr .r2).toNat s₁ := by
  have L := siLay h
  obtain ⟨hrd, -, -, -, dns, dnW, -, -, -, -, bn, -, -, -, fn, -, -, -, -⟩ := h
  refine ⟨h1.env, ?_, h1.r4, by rw [h1.r5]; simp, ⟨?_, (s₀.gpr .r2).isLt, fn, dns, dnW, bn⟩⟩
  · rw [ctxH_eq, blockAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 768 by decide))]
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (by simp)

/-- After `j0`. -/
def SI2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, SI1 s₀ s₁ ∧ J0Out (s₀.gpr .r0) (s₀.gpr .r3) (arg s₀ 0) s₀.sp (s₀.gpr .r8)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) s₁.mem s₂

theorem si_fin {s₀ s₂ : State} (h : streamInitArm.pre s₀) (h2 : SI2 s₀ s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ streamInitArm.post s₀ s' := by
  have L := siLay h
  obtain ⟨s₁, h1, ho⟩ := h2
  obtain ⟨k7, he⟩ := ho.env
  obtain ⟨-, -, -, -, -, dnW, -, -, -, -, -, -, -, -, fn, -, fW, -, -⟩ := h
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) (h1.saved.frame ho.frame (saved_j0Frame L)) he.sp)
    fun s' hh => ⟨hh.1, fun ciph => ?_⟩
  have hm := hh.2.1
  have hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega_using [])
  have hj := ho.j0; have hy := ho.y; have hcb := ho.cb
  rw [hiv] at hj hcb
  rw [Proof.Gcm.streamRepr_iff, hm, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit]
  exact ⟨hj, Proof.Gcm.absorbed_nil _ hy, Proof.Gcm.ctr_zero _ _ _ _ hcb⟩

theorem streamInit_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamInitArm.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ streamInitArm.post s₀ s' :=
  WP.seq (WP.mono (si1_wp h) fun s₁ h1 => WP.seq (WP.mono (j0_ok (siLay h) (si_j0In h h1)) fun _ ho =>
    si_fin h ⟨s₁, h1, ho⟩))

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.StreamAad`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_aad`

Untrusted: everything here is checked by Lean. `stream_aad` saves our
caller's registers in `scratch` (`W`) and absorbs the additional data into
GHASH with `absorb` (`streamAad_wp`), with `len(A) mod 16` from the low
word of `aad_len`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr)
open VG.Spec.Gcm (ctxH)

theorem saLay {s₀ : State} (h : streamAadArm.pre s₀) :
    Lay (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, -, -, dsW, -, -, bc, -, bs, bW, fc, fs, -, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SA1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) s₁
  r4 : s₁.gpr .r4 = arg s₀ 0
  r5 : s₁.gpr .r5 = arg s₀ 1
  r6 : s₁.gpr .r6 = BitVec.ofNat 32 ((s₀.gpr .r2).toNat % 16)
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : SavedAt s₁.mem (arg s₀ 2) s₀
  frame : Frame [savedR (arg s₀ 2)] s₀.mem s₁.mem

theorem sa1_wp {s₀ : State} (h : streamAadArm.pre s₀) : WP isa (.block streamAadPre) s₀ (SA1 s₀) := by
  have hp := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, fW, -, spf⟩ := hp
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r1), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 2), 768⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : ∀ i < 3, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => arg_in (n := 3) hi spf (by rw [hrd]; simp)
  have hA : ∀ r ∈ [savedR (arg s₀ 2)], (args s₀ 3).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  refine entry_ok (off := 8) (by decide) (ha 2 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have a₀ := ha 0 (by decide); have a₁ := ha 1 (by decide)
  rw [← rd, ← wr, ← sp] at a₀ a₁
  have e₀ := arg_frame (s' := s₁) sp spf fr hA (i := 0) (by decide)
  have e₁ := arg_frame (s' := s₁) sp spf fr hA (i := 1) (by decide)
  rw [stackArg_zero] at e₀
  simp only [stackArg_eq, Nat.mul_one] at e₁ a₁
  simp only [Nat.mul_zero] at a₀
  have hand := and15 (s₀.gpr .r2)
  refine WP.of_runBlock ⟨_, by arun [a₀, a₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12, hand]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · simp [gpr_setReg, e₀]
  · simp [gpr_setReg, e₁, stackArg]; rfl
  · exact rd
  · exact wr

theorem sa_absIn {s₀ s₁ : State} (h : streamAadArm.pre s₀) (h1 : SA1 s₀ s₁) {x : List Byte}
    (hx : x.length % 16 = (s₀.gpr .r2).toNat % 16) :
    AbsIn (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) 16
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) x (arg s₀ 0) (arg s₀ 1).toNat s₁ := by
  have L := saLay h
  obtain ⟨hrd, -, -, -, dDs, dDW, -, -, -, -, bD, -, -, -, -, fD, -, -, -⟩ := h
  refine ⟨h1.env, h1.r4, by rw [h1.r5]; simp, by rw [h1.r6, hx], ⟨?_, (arg s₀ 1).isLt, fD, dDs, dDW, bD⟩, ?_⟩
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (by simp)
  · rw [ctxH_eq, blockAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 768 by decide))]

/-- After `absorb`. -/
def SA2 (s₀ : State) (x : List Byte) (s₂ : State) : Prop :=
  ∃ s₁, SA1 s₀ s₁ ∧ AbsOut (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) 16
    (ctxH s₀.mem (State.addr (s₀.gpr .r0))) x (x ++ bytesAt s₁.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) s₁.mem s₂

theorem sa_fin {s₀ s₂ : State} (h : streamAadArm.pre s₀) {x : List Byte} (h2 : SA2 s₀ x s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ ∀ ciph iv,
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv x [] →
      StreamRepr s'.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv
        (x ++ bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) [] := by
  have L := saLay h
  obtain ⟨s₁, h1, ho⟩ := h2
  have he := ho.env
  obtain ⟨-, -, -, -, -, dDW, dsW, -, -, -, -, -, -, -, -, fD, fW, -, -⟩ := h
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) (h1.saved.frame ho.frame (saved_absFrame L (.inr rfl)))
    he.sp) fun s' hh => ⟨hh.1, fun ciph iv hs => ?_⟩
  have hm := hh.2.1
  have hd : bytesAt s₁.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))) (by omega_using [])
  have hab := ho.abs
  rw [hd] at hab
  have dS : ∀ {d : Nat}, d + 16 ≤ 80 → ∀ r ∈ [savedR (arg s₀ 2)],
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w hd (.inr ⟨by decide, by decide⟩)
  have dA : ∀ {d : Nat}, (d = 0 ∨ d = 48 ∨ d = 64) → ∀ r ∈ absFrame (s₀.gpr .r1) (arg s₀ 2) s₀.sp 16,
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact Lay.st_st (by omega_using [hd]) (by omega_using [hd]) (by decide)
    · exact L.st_w (by omega_using [hd]) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega_using [hd])).symm
  have keep : ∀ {d : Nat}, (d = 0 ∨ d = 48 ∨ d = 64) →
      blockAt s'.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d) =
        blockAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d) := fun hd => by
    rw [hm, blockAt_frame ho.frame (dA hd), blockAt_frame h1.frame (dS (by omega_using [hd]))]
  rw [Proof.Gcm.streamRepr_iff] at hs ⊢
  obtain ⟨hj, ha, hc⟩ := hs
  simp only [ofNat_lit] at hj ha hc ⊢
  refine ⟨by simpa using (keep (d := 0) (.inl rfl)).trans (by simpa using hj), ?_, ?_⟩
  · rw [hm]
    refine hab (ha.congr ?_ ?_)
    · rw [blockAt_frame h1.frame (dS (by decide))]
    · rw [bytesAt_frame h1.frame (fun r hr => (dS (d := 32) (by decide) r hr).sub_left
        (Region.sub_prefix (by have := Nat.mod_lt (Spec.Gcm.ghashInput x []).length (show 16 > 0 by decide); omega_using [])))
        (by have := Nat.mod_lt (Spec.Gcm.ghashInput x []).length (show 16 > 0 by decide); omega_using [])]
  · exact hc.congr (keep (.inr (.inl rfl))) (keep (.inr (.inr rfl)))

theorem sa_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamAadArm.pre s₀) {x : List Byte} (hx : x.length % 16 = (s₀.gpr .r2).toNat % 16) :
    WP isa streamAad s₀ fun s' => abiPreserved s₀ s' ∧ ∀ ciph iv,
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv x [] →
      StreamRepr s'.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv
        (x ++ bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) [] :=
  WP.seq (WP.mono (sa1_wp h) fun s₁ h1 => WP.seq (WP.mono (absorb_ok (saLay h) (.inr rfl) (sa_absIn h h1 hx))
    fun _ ho => sa_fin h ⟨s₁, h1, ho⟩))

theorem streamAad_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamAadArm.pre s₀) :
    WP isa streamAad s₀ fun s' => abiPreserved s₀ s' ∧ streamAadArm.post s₀ s' := by
  have h₀ := sa_run h (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : (Block → Block) × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) i.1 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.2.1 i.2.2 [] ∧
        (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.2.2.length)
    fun i hi => WP.mono (sa_run h (x := i.2.2) (low_mod16 hi.2).symm) fun _ hh => hh.2 i.1 i.2.1 hi.1)
    fun s' hh => ⟨hh.1, fun ciph iv a hs hl => hh.2 ⟨ciph, iv, a⟩ ⟨hs, hl⟩⟩

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

theorem streamInit_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamInitArm.pre s₀) (h0' : streamInitArm.pre s₀')
    (hq : streamInitArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅⟩ := hq
  have L := siLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : ∀ {t : State}, streamInitArm.pre t → ∀ r ∈ t.wr, (args t 1).Disjoint r := fun {t} ht r hr => by
    obtain ⟨-, hwr, -, -, -, -, -, dsA, dWA, -⟩ := ht
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsA.symm
    · exact dWA.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] (4 * 1)) (.block streamInitPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SI1 s₀) (G' := SI1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 1)) (c := .block streamInitPre)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 1 s).agree (ArgsKeep.refl 1 s') q₀ spf (fun i hi => by
        obtain rfl : i = 0 := by omega_using [hi]
        exact q₅) (hw h0) (hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact si1_wp h0) (fun s e => by rw [e]; exact si1_wp h0')
  have hlt := (s₀.gpr .r2).isLt
  have b := rel_wp (F := SI1 s₀) (F' := SI1 s₀') (G := SI2 s₀) (G' := SI2 s₀')
    (rel_of_ct (j0_ct L (Np := s₀.gpr .r1) (n := (s₀.gpr .r2).toNat) hlt) (fun s h1 => ⟨_, _, _, si_j0In h0 h1⟩)
      (fun s h1 => by
        have := si_j0In h0' h1
        rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₀] at this
        exact ⟨_, _, _, this⟩))
    (fun s h1 => WP.mono (j0_ok (siLay h0) (si_j0In h0 h1)) fun s' ho => ⟨s, h1, ho⟩)
    (fun s h1 => WP.mono (j0_ok (siLay h0') (si_j0In h0' h1)) fun s' ho => ⟨s, h1, ho⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := taint) (P := fun s₁ s₂ => SI2 s₀ s₁ ∧ SI2 s₀' s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨_, e₁⟩ := h₁.env; obtain ⟨_, e₂⟩ := h₂.env
      rw [e₁.r11, e₂.r11, q₅]) hB
  exact a.seq (b.seq c)

theorem streamInit_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamInitArm.pre streamInitArm.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamInit_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem streamAad_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : streamAadArm.pre s₀) (h0' : streamAadArm.pre s₀')
    (hq : streamAadArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamAad fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have L := saLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : ∀ {t : State}, streamAadArm.pre t → ∀ r ∈ t.wr, (args t 3).Disjoint r := fun {t} ht r hr => by
    obtain ⟨-, hwr, -, -, -, -, -, dsA, dWA, -⟩ := ht
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsA.symm
    · exact dWA.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] (4 * 3)) (.block streamAadPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SA1 s₀) (G' := SA1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 3)) (c := .block streamAadPre)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 3 s).agree (ArgsKeep.refl 3 s') q₀ spf (fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
        · exact q₅
        · exact q₆
        · exact q₇) (hw h0) (hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact sa1_wp h0) (fun s e => by rw [e]; exact sa1_wp h0')
  have b := rel_wp (F := SA1 s₀) (F' := SA1 s₀') (G := fun s => ∃ x, SA2 s₀ x s) (G' := fun s => ∃ x, SA2 s₀' x s)
    (rel_of_ct (absorb_ct L (yo := 16) (.inr rfl) (D := arg s₀ 0) (n := (arg s₀ 1).toNat)
      (q := (s₀.gpr .r2).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s h1 => ⟨_, _, _, _, by simp, sa_absIn h0 h1 (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0) (by simp)⟩)
      (fun s h1 => by
        have := sa_absIn h0' h1 (x := List.replicate ((s₀'.gpr .r2).toNat % 16) 0) (by simp)
        rw [← q₁, ← q₂, ← q₃, ← q₅, ← q₆, ← q₇, ← q₀] at this
        exact ⟨_, _, _, _, by simp, this⟩))
    (fun s h1 => WP.mono (absorb_ok L (.inr rfl) (sa_absIn h0 h1 (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
      (by simp))) fun s' ho => ⟨_, s, h1, ho⟩)
    (fun s h1 => WP.mono (absorb_ok (saLay h0') (.inr rfl) (sa_absIn h0' h1
      (x := List.replicate ((s₀'.gpr .r2).toNat % 16) 0) (by simp))) fun s' ho => ⟨_, s, h1, ho⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := taint) (P := fun s₁ s₂ => (∃ x, SA2 s₀ x s₁) ∧ ∃ x, SA2 s₀' x s₂)
    (c := .block restore) (Taint.ofRegs [.r11]) (fun s₁ s₂ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩⟩ =>
      Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h₁.env.r11, h₂.env.r11, q₇]) hB
  exact a.seq (b.seq c)

theorem streamAad_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa streamAadArm.pre streamAadArm.pub streamAad :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamAad_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.CTOpen`, which only this module used -/

section

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_seal` and `vg_sm4_gcm_open` are constant time

Untrusted: everything here is checked by Lean. `open` decrypts only if the
tags are equal, which its contract makes public: the comparison, done
without a branch, is related across the runs by what each run computes
(`rel_ghost`, `open_head`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm

theorem one_entry_agree {n wi : Nat} {rs : List Reg} (hrs : ∀ r ∈ rs, r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3)
    {s₀ s₀' : State} (h0 : onePre n wi s₀) (h0' : onePre n wi s₀') (hq : onePub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (argTaint rs (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 qa (one_hw h0) (one_hw h0') fun r hr => ?_
  rcases hrs r hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : sealArm.pre s₀) (h0' : sealArm.pre s₀') (hq : sealArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «seal» fun _ _ => True := by
  obtain h5 : onePre 5 4 s₀ := sealPreArm.one h0
  obtain h5' : onePre 5 4 s₀' := sealPreArm.one h0'
  have hq6 : onePub 5 s₀ s₀' := hq
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  obtain L := oneLay h5
  have spf := h5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf' := h5'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SO1 5 4 s₀) (G' := SO1 5 4 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 5)) (c := .block (oneEntry 16))
    (one_entry_agree (by simp) h5 h5' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact one1_wp h5 (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact one1_wp h5' (by decide) (by decide) fun _ h => h)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 4
  obtain c := rel_agree (F := OF 5 4 s₀ s₀) (F' := OF 5 4 s₀ s₀') (G := W) (G' := W) (argTaint [.r11] (4 * 5))
    (c := .block (tagOut 12))
    (fun s s' ⟨_, he, hk⟩ ⟨_, he', hk'⟩ => hk.agree hk' q₀ spf qa (one_hw h5) (one_hw h5') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (ti := 3) (by decide) (.inr rfl) rfl he hk spf h5.1.2.2.2 (by rw [hwr]; simp) fT
      (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨_, he, hk⟩ => tagOut_wp L (ti := 3) (by decide) (.inr rfl) rfl he hk spf' h5'.1.2.2.2 (by rw [hwr']; simp) fT'
      (by rw [qa 4 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  obtain d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2]) hB
  exact a.seq ((oneAad_rel h5 h5' hq6 (by decide) (by decide)).seq ((oneCrypt_rel h5 h5' hq6 (by decide) (by decide)).seq
    ((oneTag_rel h5 h5' hq6 (by decide) (by decide) (.inl rfl)).seq (c.seq d))))

theorem seal_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `open` -/

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (arg t 4).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  obtain e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Sm4.Gcm.ctxCiph t.mem (State.addr (t.gpr .r0)))
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (State.addr (t.gpr .r0)))
          (Spec.Aes.bytesAt t.mem (State.addr (t.gpr .r1)) (t.gpr .r2).toNat)))
        (Spec.Aes.bytesAt t.mem (State.addr (arg t 1)) (arg t 2).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), decide_eq_true h]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_false h]; rfl

theorem open1_wp {t₀ : State} (h : onePre 6 5 t₀) :
    WP isa (.block (oneEntry 20 ++ ([.ldrSp .r6 16] : List Instr))) t₀ fun s =>
      SO1 6 5 t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg t₀ 4).toNat := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args t₀ 6 ∈ t₀.rd := h.1.2.2.2
  refine WP.block_append (one1_wp h (by decide) (by decide) fun s₁ h1 => ?_)
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
  exact ⟨h1.keep (fun r _ b => by simp [gpr_setReg, b]) ⟨rfl, rfl, rfl, rfl⟩, by simp [gpr_setReg, v5]⟩

section
variable {c st w sp k8 : BitVec 32} {t₀ : State}

theorem blk_wp {s : State} (h : P7 6 c st w sp k8 t₀ s) :
    WP isa (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) s (FT 6 t₀ c st w sp k8) := by
  obtain ⟨⟨k7, he, hk⟩, -⟩ := h
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  exact ⟨_, he.set7 rfl (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_subFlags, gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem mov07_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (.reg .r7)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

end

theorem open_rel [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₀' : State} (h0 : openArm.pre s₀) (h0' : openArm.pre s₀') (hq : openArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «open» fun _ _ => True := by
  obtain h6 : onePre 6 5 s₀ := openPreArm.one h0
  obtain h6' : onePre 6 5 s₀' := openPreArm.one h0'
  have hq6 : onePub 6 s₀ s₀' := hq.1
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  obtain L := oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ 6 ∈ s₀.rd := h6.1.2.2.2
  have hin' : args s₀' 6 ∈ s₀'.rd := h6'.1.2.2.2
  obtain e4 : arg s₀' 5 = arg s₀ 5 := (qa 5 (by decide)).symm
  have hrd := h0.1
  have hrd' := h0'.1
  have tW := h0.2.2.2.2.2.2.2.2.2.2.2.1
  have tW' := h0'.2.2.2.2.2.2.2.2.2.2.2.1
  have fT := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fT' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain h5' : (arg s₀' 4).toNat = (arg s₀ 4).toNat := by rw [qa 4 (by decide)]
  let W : State → Prop := fun s => s.gpr .r11 = arg s₀ 5
  obtain r11 : ∀ {t₀ s : State}, OF 6 5 s₀ t₀ s → W s := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  let G1 : State → State → Prop := fun t₀ s => SO1 6 5 t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (arg s₀ 4).toNat
  obtain a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G1 s₀) (G' := G1 s₀')
    (argTaint [.r0, .r1, .r2, .r3] (4 * 6)) (c := .block (oneEntry 20 ++ [.ldrSp .r6 16]))
    (one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact open1_wp h6)
    (fun s e => by rw [e]; exact WP.mono (open1_wp h6') fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, h5']⟩)
  let G2 : State → State → Prop := fun t₀ s => SO1 6 5 t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (arg s₀ 4).toNat
  obtain tl : ∀ {t₀ s : State}, G1 t₀ s → WP isa tagLenOk s (G2 t₀) := fun {t₀ s} ⟨h1, h6r⟩ =>
    WP.mono (tagLenOk_ok h6r (arg s₀ 4).isLt) fun s' ⟨hz, g, k⟩ => ⟨h1.keep (fun r a _ => g r a) k, hz⟩
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  obtain b := rel_wp (F := G1 s₀) (F' := G1 s₀') (G := G2 s₀) (G' := G2 s₀')
    (RelCT.taint (A := taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tl h) (fun s h => tl h)
  -- the branches
  let rest6 : Prog isa := .seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.block [])
  let rest5 : Prog isa := .seq (cmp uO) rest6
  let rest4 : Prog isa := .seq (recv 12) rest5
  let rest3 : Prog isa := .seq (.block [.ldrSp .r6 16]) rest4
  let rest2 : Prog isa := .seq (oneTag uO) rest3
  let Z : State → State → Prop := fun t₀ s => s.z = decide (¬openTagOk t₀)
  obtain mid : RelCT isa (fun a b => G2 s₀ a ∧ G2 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) openGood) fun a b => W a ∧ W b := by
    refine rel_iteQ (!Spec.Gcm.tagLenOk (arg s₀ 4).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := G2 s₀) (F' := G2 s₀') (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => mov0_wp h.1.env.r11) (fun s h => mov0_wp (by rw [h.1.env.r11, e4]))
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 4).toNat = true := by simpa using hb
      obtain hok' : Spec.Gcm.tagLenOk (arg s₀' 4).toNat = true := by rw [h5']; exact hok
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      obtain eZ : decide (¬openTagOk s₀') = decide (¬openTagOk s₀) := by
        rw [decide_not, decide_not, ← openRes_isSome hok, ← openRes_isSome hok', hq.2]
      -- what each run reaches: whether the tags are equal
      obtain pfx : ∀ {t₀ s : State}, openPreArm t₀ → Spec.Gcm.tagLenOk (arg t₀ 4).toNat = true → SO1 6 5 t₀ s →
          WP isa (.seq oneAad rest2) s (Z t₀) := fun ht hk h2 =>
        open_head ht h2 hk (T := .block []) fun s₈ om => WP.block_nil om.z
      obtain y1 := rel_ghost (R := rest2) (Z := Z s₀) (Z' := Z s₀') (oneAad_rel h6 h6' hq6 (by decide) (by decide))
      obtain y2 := rel_ghost (R := rest3) (Z := Z s₀) (Z' := Z s₀')
        (oneTag_rel h6 h6' hq6 (by decide) (by decide) (o := uO) (.inr rfl))
      obtain y3 := rel_ghost (R := rest4) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := OF 6 5 s₀ s₀) (F' := OF 6 5 s₀ s₀')
          (G := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀)
          (G' := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀')
          (argTaint [] (4 * 6)) (c := .block [.ldrSp .r6 16])
          (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6') (rs := [])
            (by simp)) ⟨_, by taint_decide⟩
          (fun s h => ld6_wp (ti := 4) (by decide) rfl (.inr rfl) spf hin rfl h) (fun s h => ld6_wp (ti := 4) (by decide) rfl (.inr rfl) spf' hin' h5' h))
      obtain hD : ∀ {d k : Nat}, d + k ≤ 768 →
          (args s₀ 6).Disjoint ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h6.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain hD' : ∀ {d k : Nat}, d + k ≤ 768 →
          (args s₀' 6).Disjoint ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => by
        rw [← e4]; exact (h6'.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain y4 := rel_ghost (R := rest5) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree
          (F := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀)
          (F' := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀')
          (G := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀)
          (G' := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀')
          (argTaint [.r6, .r11] (4 * 6)) (c := recv 12)
          (fun s s' h h' => h.1.choose_spec.2.agree h'.1.choose_spec.2 q₀ spf qa (one_hw h6) (one_hw h6')
            fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · rw [h.2, h'.2]
              · rw [r11 h.1, r11 h'.1]) ⟨_, by taint_decide⟩
          (fun s h => recv_wp L (ti := 3) (by decide) (.inr rfl) rfl spf hin (hD (by decide)) (by rw [hrd]; simp) fT
            (tW.sub_right (Lay.wSub (by decide))) t1 t16 h)
          (fun s h => recv_wp L (ti := 3) (by decide) (.inr rfl) rfl spf' hin' (hD' (by decide)) (by rw [hrd', h5']; simp)
            (by rw [← h5']; exact fT') (by rw [← h5', ← e4]; exact tW'.sub_right (Lay.wSub (by decide)))
            t1 t16 h))
      obtain ⟨_, c5⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp uO) h).isSome = true :=
        ⟨_, by taint_decide⟩
      obtain y5 := rel_ghost (R := rest6) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp
          (F := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀)
          (F' := P6 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) (arg s₀ 4).toNat s₀')
          (G := P7 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) s₀)
          (G' := P7 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h.2.2]
            · rw [r11 h.1.1, r11 h.2.1]) c5)
          (fun s h => cmp_wp L spf (.inr rfl) (hD (by decide)) t1 t16 h)
          (fun s h => cmp_wp L spf' (.inr rfl) (hD' (by decide)) t1 t16 h))
      obtain ⟨_, c6⟩ : ∃ h, (taint.check (Taint.ofRegs [])
          (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
      obtain y6 := rel_ghost (R := .block []) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := P7 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) s₀)
          (F' := P7 6 (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₀.gpr .r3) s₀')
          (G := OF 6 5 s₀ s₀) (G' := OF 6 5 s₀ s₀')
          (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp at hr) c6)
          (fun s h => blk_wp h) (fun s h => blk_wp h))
      -- the data decrypted only if the tags are equal, which is public
      obtain y7 : RelCT isa (fun a b => (OF 6 5 s₀ s₀ a ∧ WP isa (.block []) a (Z s₀)) ∧
          (OF 6 5 s₀ s₀' b ∧ WP isa (.block []) b (Z s₀'))) (.ite .eq (.block []) oneCrypt) fun a b => W a ∧ W b :=
        rel_iteQ (decide (¬openTagOk s₀)) (fun s h => wp_nil h.2) (fun s h => (wp_nil h.2).trans eZ)
          (fun _ => RelCT.block_nil fun x y h => ⟨r11 h.1.1, r11 h.2.1⟩)
          (fun _ => (oneCrypt_rel h6 h6' hq6 (by decide) (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
            fun _ _ h => ⟨r11 h.1, r11 h.2⟩)
      obtain ⟨_, c8⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block [.mov .r0 (.reg .r7)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      obtain y8 := rel_wp (F := W) (F' := W) (G := W) (G' := W)
        (RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) c8)
        (fun s h => mov07_wp h) (fun s h => mov07_wp h)
      refine RelCT.mono (y1.seq (y2.seq (y3.seq (y4.seq (y5.seq (y6.seq (y7.seq y8))))))) (fun s s' h => ?_)
        fun _ _ h => h
      exact ⟨⟨h.1.1, pfx h0 hok h.1.1⟩, ⟨h.2.1, pfx h0' hok' h.2.1⟩⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  obtain d := RelCT.taint (A := taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem open_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa openArm.pre openArm.pub «open» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.InitCT`, which only this module used -/

section

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The blocks are checked by the
taint analysis, from the registers the correctness proof pins (the
arguments, then `r9` and `r11`); the calls of `vg_sm4_expand_key` and
`vg_sm4_ctr32` are constant time by their own proofs (`key_rel`, `ctr_rel`),
with the same arguments in both runs.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

theorem IS4.r11 {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : IS4 s₀ s₄) : s₄.gpr .r11 = s₀.gpr .r2 := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨-, -, -, -, -, -, -, g11, -⟩ := h3.facts h
  rw [cp.saved _ (by decide) (by decide), g11]

theorem init_rel {s₀ s₀' : State} (h0 : initArm.pre s₀) (h0' : initArm.pre s₀') (hq : initArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃⟩ := hq
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := IS1 s₀) (G' := IS1 s₀') (c := .block initPre)
    (Taint.ofRegs [.r0, .r1, .r2])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact is1_wp h0) (fun s e => by rw [e]; exact is1_wp h0')
  have b := rel_wp (F := IS1 s₀) (F' := IS1 s₀') (G := IS2 s₀) (G' := IS2 s₀')
    (key_rel fun s₁ s₂ h => ⟨_, _, init_kc h0 h.1, by have := init_kc h0' h.2; rwa [← q₁, ← q₂] at this,
      by rw [h.1.sp, h.2.sp, q₀]⟩)
    (fun s₁ h1 => WP.mono (key_call (init_kc h0 h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
    (fun s₁ h1 => WP.mono (key_call (init_kc h0' h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
  have c := rel_agree (F := IS2 s₀) (F' := IS2 s₀') (G := IS3 s₀) (G' := IS3 s₀') (c := .block initArgs)
    (Taint.ofRegs [.r9, .r11])
    (fun s s' e e' => by
      obtain ⟨g9, g11, -⟩ := e.g
      obtain ⟨g9', g11', -⟩ := e'.g
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g9, g9', q₂]
      · rw [g11, g11', q₃]) ⟨_, by taint_decide⟩
    (fun s e => by obtain ⟨s₃, run⟩ := is3_run h0 e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
    (fun s e => by obtain ⟨s₃, run⟩ := is3_run h0' e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
  have d := rel_wp (F := IS3 s₀) (F' := IS3 s₀') (G := IS4 s₀) (G' := IS4 s₀')
    (ctr_rel fun s₁ s₂ h => ⟨_, _, _, _, init_cc h0 h.1,
      by have := init_cc h0' h.2; rwa [← q₂, ← q₃] at this,
      by obtain ⟨-, -, -, -, -, -, -, -, -, -, e⟩ := h.1.facts h0
         obtain ⟨-, -, -, -, -, -, -, -, -, -, e'⟩ := h.2.facts h0'
         rw [e, e', q₀]⟩)
    (fun s₃ h3 => WP.mono (ctr_call (init_cc h0 h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
    (fun s₃ h3 => WP.mono (ctr_call (init_cc h0' h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => IS4 s₀ s₁ ∧ IS4 s₀' s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r11 h0, h.2.r11 h0', q₃]) hB
  exact a.seq (b.seq (c.seq (d.seq e)))

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.Verified`, which only this module used -/

section

/-! ### `Sm4Gcm.Arm.Scratch`, which only this module used -/

section

/-!
# SM4-GCM on ARMv7: the functions with their working space as an argument

The ARMv7 SM4-GCM functions keep their 768-byte working space in a frame of
their own (`Verified.stackScratch`, `Verified.regScratch`), around code
proved with the working space as a last argument: `initScratchContract`, …,
`openScratchContract` are the shared contracts with a 768-byte `scratch` (or
`work`) buffer appended, whatever it holds (`Proof/Sm4Gcm/Scratch.lean` has
x86-64's, with 2560 bytes).

The frames also hold a copy of the arguments passed on the stack, which needs
the postconditions to read the memory on entry only within the function's
buffers: `Proof/Sm4Gcm/Scratch.lean` proves it, and
`Proof/AesGcm/Scratch.lean` of `vg_sm4_gcm_stream_init`'s and
`vg_sm4_gcm_stream_aad`'s, which are AES-GCM's.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG.Spec.Sm4.Gcm

/-- `vg_sm4_gcm_init` with `scratch: *mut [u64; 96]`. -/
def initScratchSig : Sig where
  params := initSig.params ++ [("scratch", .array true .u64 96)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (post := fun key ctx _scratch => initPost A.ptrBits key ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_init` with `scratch: *mut [u64; 96]`. -/
def streamInitScratchSig : Sig where
  params := Spec.Gcm.streamInitSig.params ++ [("scratch", .array true .u64 96)]

/-- `Spec.Gcm.streamInitContract`, whatever `scratch` is. -/
def streamInitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitScratchSig.contract A
    (post := fun ctx nonce nonceLen state _scratch =>
      Spec.Gcm.streamInitPost A.ptrBits ctx nonce nonceLen state)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_aad` with `scratch: *mut [u64; 96]`. -/
def streamAadScratchSig : Sig where
  params := Spec.Gcm.streamAadSig.params ++ [("scratch", .array true .u64 96)]

/-- `Spec.Gcm.streamAadContract`, whatever `scratch` is. -/
def streamAadScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamAadScratchSig.contract A
    (post := fun ctx state aadLen data len _scratch =>
      Spec.Gcm.streamAadPost A.ptrBits ctx state aadLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` with
`scratch: *mut [u64; 96]`. -/
def streamCryptScratchSig : Sig where
  params := streamCryptSig.params ++ [("scratch", .array true .u64 96)]

/-- `streamEncryptContract`, whatever `scratch` is. -/
def streamEncryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptContract`, whatever `scratch` is. -/
def streamDecryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_finish` with `work: *mut [u64; 96]`. -/
def streamFinishScratchSig : Sig where
  params := streamFinishSig.params ++ [("work", .array true .u64 96)]

/-- `streamFinishContract`, whatever `work` is. -/
def streamFinishScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishScratchSig.contract A
    (post := fun ctx state aadLen textLen tag _work =>
      streamFinishPost A.ptrBits ctx state aadLen textLen tag)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_verify` with `work: *mut [u64; 96]`. -/
def streamVerifyScratchSig : Sig where
  params := streamVerifySig.params ++ [("work", .array true .u64 96)]
  ret := some .u32

/-- `streamVerifyContract`, whatever `work` is. -/
def streamVerifyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyScratchSig.contract A
    (post := fun ctx state aadLen textLen tag tagLen _work =>
      streamVerifyPost A.ptrBits ctx state aadLen textLen tag tagLen)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_seal` with `work: *mut [u64; 96]`. -/
def sealScratchSig : Sig where
  params := sealSig.params ++ [("work", .array true .u64 96)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_open` with `work: *mut [u64; 96]`. -/
def openScratchSig : Sig where
  params := openSig.params ++ [("work", .array true .u64 96)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)

end VG.Proof.Sm4Gcm.Arm

end

end


/-!
# SM4-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as a last argument
(`Proof/Sm4Gcm/Arm/Scratch.lean`), with 1520 bytes of stack: those of
`vg_sm4_ctr32`'s frame, the most any call uses (`vg_sm4_expand_key` uses
1456, and each call of `vg_ghash` pushes two words).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying `vg_sm4_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 768⟩]

theorem init_verified : Verified Arm.target init (Proof.Sm4Gcm.Arm.initScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.initScratchContract, Proof.Sm4Gcm.Arm.initScratchSig, Spec.Sm4.Gcm.initSig,
      Spec.Sm4.Gcm.initPost, initArm, bel, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] [initSat, mkSat] using initSat)

/-- A state satisfying `vg_sm4_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamInit_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamInit (Proof.Sm4Gcm.Arm.streamInitScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamInit_wp hs) streamInit_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamInitScratchContract, Proof.Sm4Gcm.Arm.streamInitScratchSig,
      Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost, streamInitArm, bel, arg, args, arg64,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using siSat)

/-- A state satisfying `vg_sm4_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

theorem streamAad_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamAad (Proof.Sm4Gcm.Arm.streamAadScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamAad_wp hs) streamAad_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamAadScratchContract, Proof.Sm4Gcm.Arm.streamAadScratchSig,
      Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost, streamAadArm, bel, arg, args, arg64,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using saSat)

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 768⟩]

theorem streamEncrypt_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamEncrypt (Proof.Sm4Gcm.Arm.streamEncryptScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamEncrypt_wp hs) streamEncrypt_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamEncryptScratchContract, Proof.Sm4Gcm.Arm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamEncryptPost, streamEncryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamDecrypt (Proof.Sm4Gcm.Arm.streamDecryptScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamDecrypt_wp hs) streamDecrypt_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamDecryptScratchContract, Proof.Sm4Gcm.Arm.streamCryptScratchSig,
      Spec.Sm4.Gcm.streamCryptSig, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

/-- `mkSat`, with the stack argument 2 (at `0x8008`) `0x4000`. -/
def mkSat2 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x8009 then 0x40 else 0 }

/-- `mkSat`, with the stack argument 3 (at `0x800c`) `0x4000`. -/
def mkSat3 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x800D then 0x40 else 0 }

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition (with `tag` at `0x4000` and `work`
at 0). -/
def fSat : State :=
  mkSat2 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩, ⟨0, 768⟩]

theorem streamFinish_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamFinish (Proof.Sm4Gcm.Arm.streamFinishScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamFinish_wp hs) streamFinish_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.streamFinishScratchContract, Proof.Sm4Gcm.Arm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost, streamFinishArm, streamFinishPreArm,
      finPub, bel, arg, args, arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat2, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using fSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def vSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 768⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamVerify (Proof.Sm4Gcm.Arm.streamVerifyScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => streamVerify_wp hs) streamVerify_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [streamVerifyArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro iv a c hs ha hc
        rw [e]
        exact h iv a c hs ha hc
      pub := by
        sig_implies_pub [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.Arm.streamVerifyScratchContract, Proof.Sm4Gcm.Arm.streamVerifyScratchSig,
          Spec.Sm4.Gcm.streamVerifySig, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args,
          arg64, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using vSat }

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce, additional data or
data, `tag` at `0x4000` and `work` at 0). -/
def oSat : State :=
  mkSat3 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0, 768⟩]

theorem seal_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «seal» (Proof.Sm4Gcm.Arm.sealScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.Sm4Gcm.Arm.sealScratchContract, Proof.Sm4Gcm.Arm.sealScratchSig, Spec.Sm4.Gcm.sealSig,
      Spec.Sm4.Gcm.sealPost, sealArm, sealPreArm, onePub, bel, arg, args, arg64, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat3, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using oSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition (with no nonce, additional data, data
or tag, and `work` at 0). -/
def opSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0, 768⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «open» (Proof.Sm4Gcm.Arm.openScratchContract Arm.abi 1520) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig,
          Spec.Sm4.Gcm.openSig, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig, Spec.Sm4.Gcm.openSig,
          Spec.Sm4.Gcm.openLeak, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
      sat := by
        sig_implies_sat [Proof.Sm4Gcm.Arm.openScratchContract, Proof.Sm4Gcm.Arm.openScratchSig,
          Spec.Sm4.Gcm.openSig, openArm, openPreArm, onePub, bel, arg, args, arg64, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using opSat }

end VG.Proof.Sm4Gcm.Arm

end

end


/-!
# SM4-GCM on ARMv7, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it.
`init`'s working space is its third argument, in `r2`: its frame is the 768
bytes of working space (`Verified.regScratch`). That of the others is passed
on the stack: the frames of 784 bytes of `stream_init` and `stream_aad` hold
the copies of the other arguments passed on the stack (none for
`stream_init`, `data` and `len` for `stream_aad`), the buffer's address and
the saved `lr` too (`Verified.stackScratch`); so do the frames of 800 bytes
of `stream_encrypt` and `stream_decrypt`, with copies of their four words of
stack arguments (`text_len`, `data` and `len`), of `stream_finish` (three:
`text_len` and `tag`), of `stream_verify` and `seal` (four) and of `open`
(five). The copies are read only where the postconditions read the buffers
(`Proof/Sm4Gcm/Scratch.lean`, `Arm/Scratch.lean`). Each frame sits on the
1520 bytes of stack the code needs below it.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract Arm.abi 2288).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, mkSat] using initFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 768 .r2 init)
    (Spec.Sm4.Gcm.initContract Arm.abi 2288) :=
  Arm.Verified.regScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 96)
    (post := Spec.Sm4.Gcm.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 1520) init_verified (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => initPostOut_local _ vs mm m₁ m₂ r hl) initFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩] [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract Arm.abi 2304).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamInitFrameSat, mkSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 784 0 streamInit)
      (Spec.Gcm.streamInitContract Arm.abi 2304) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Gcm.streamInitPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 0) streamInit_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamInitPost_local _)
    (fun vs mm m₁ m₂ r hl _ => Proof.AesGcm.streamInitPostOut_local _ vs mm m₁ m₂ r hl)
    streamInitFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 8⟩] [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract Arm.abi 2304).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamAadFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 784 2 streamAad)
      (Spec.Gcm.streamAadContract Arm.abi 2304) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Gcm.streamAadPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 2) streamAad_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamAadPost_local _)
    (fun vs mm m₁ m₂ r hl _ => Proof.AesGcm.streamAadPostOut_local _ vs mm m₁ m₂ r hl)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space: their four words of
stack arguments at `0x8000`. -/
def crFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩]

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamEncrypt)
      (Spec.Sm4.Gcm.streamEncryptContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamEncryptPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamEncrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamEncryptPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamEncryptPostOut_local _ vs mm m₁ m₂ r hl)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using crFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamDecrypt)
      (Spec.Sm4.Gcm.streamDecryptContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamDecryptPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamDecryptPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamDecryptPostOut_local _ vs mm m₁ m₂ r hl)
    streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without the
working space: its three words of stack arguments at `0x8000`. -/
def finFrameSat : State :=
  mkSat2 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩]

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig, Spec.Sm4.Gcm.streamFinishPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat2, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 3 streamFinish)
      (Spec.Sm4.Gcm.streamFinishContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamFinishPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 3) streamFinish_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamFinishPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamFinishPostOut_local _ vs mm m₁ m₂ r hl) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def verFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] [⟨0x3000, 80⟩]

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig, Spec.Sm4.Gcm.streamVerifyPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 streamVerify)
      (Spec.Sm4.Gcm.streamVerifyContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.streamVerifyPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) streamVerify_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamVerifyPost_local _)
    (fun vs mm m₁ m₂ r hl _ => streamVerifyPostOut_local _ vs mm m₁ m₂ r hl) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: its four words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  mkSat3 (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 16⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat3, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 4 «seal»)
      (Spec.Sm4.Gcm.sealContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (m := 4) seal_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (sealPost_local _)
    (fun vs mm m₁ m₂ r hl _ => sealPostOut_local _ vs mm m₁ m₂ r hl) sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: its five words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract Arm.abi 2320).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 800 5 «open»)
      (Spec.Sm4.Gcm.openContract Arm.abi 2320) :=
  Arm.Verified.stackScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 96) (post := Spec.Sm4.Gcm.openPost Arm.abi.ptrBits) (wa := true) (stack := 1520)
    (leak := some (Spec.Sm4.Gcm.openLeak Arm.abi.ptrBits))
    (m := 5) open_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (openPost_local _)
    (fun vs mm m₁ m₂ r hl _ => openPostOut_local _ vs mm m₁ m₂ r hl) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.Sm4Gcm.Arm
