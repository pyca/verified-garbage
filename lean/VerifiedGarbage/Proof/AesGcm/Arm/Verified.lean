module

public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Proof.AesGcm.Arm.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.Arm.Init
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.Arm.Init
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTFn
import VerifiedGarbage.Proof.AesGcm.Arm.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Proof.AesGcm.Arm.Args
meta import VerifiedGarbage.Proof.AesGcm.Arm.Contract
meta import VerifiedGarbage.Proof.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.AesGcm.Arm.Args

/-! ### `AesGcm.Arm.CTStream`, which only this module used -/

section

/-! ### `AesGcm.Arm.StreamInit`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. `stream_init` saves our
caller's registers in `scratch` (`W`) and writes the state's `J₀`, its zero
accumulator and its first counter block with `j0` (`streamInit_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)

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
  have hW : Covers [⟨State.addr (arg s₀ 0), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
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
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 2560 by decide))]
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

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.StreamAad`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. `stream_aad` saves our
caller's registers in `scratch` (`W`) and absorbs the additional data into
GHASH with `absorb` (`streamAad_wp`), with `len(A) mod 16` from the low
word of `aad_len`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)

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
  have hW : Covers [⟨State.addr (arg s₀ 2), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
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
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 2560 by decide))]

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

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

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

end VG.Proof.AesGcm.Arm

end

end

/-! ### `AesGcm.Arm.InitCT`, which this module and modules that import it used -/

section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The blocks are checked by the
taint analysis, from the registers the correctness proof pins (the
arguments, then `r8`, `r9` and `r11`); the calls of `vg_aes_expand_key_scratch` and
`vg_aes_ctr32` are constant time by their own proofs (`key_rel`, `ctr_rel`),
with the same arguments in both runs.
-/

@[expose] public section

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem IS4.r11 {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : IS4 s₀ s₄) : s₄.gpr .r11 = s₀.gpr .r3 := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨-, -, -, -, -, -, -, -, -, g11, -⟩ := h3.facts h
  rw [cp.saved _ (by decide) (by decide), g11]

theorem init_rel {s₀ s₀' : State} (h0 : initArm.pre s₀) (h0' : initArm.pre s₀') (hq : initArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  have eR : initR s₀' = initR s₀ := by simp only [initR, q₂]
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := IS1 s₀) (G' := IS1 s₀') (c := .block initPre)
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact is1_wp h0) (fun s e => by rw [e]; exact is1_wp h0')
  have b := rel_wp (F := IS1 s₀) (F' := IS1 s₀') (G := IS2 s₀) (G' := IS2 s₀')
    (key_rel fun s₁ s₂ h => ⟨_, _, _, _, init_kc h0 h.1, by have := init_kc h0' h.2; rwa [← q₁, ← q₂, ← q₃, ← q₄] at this⟩)
    (fun s₁ h1 => WP.mono (key_call (init_kc h0 h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
    (fun s₁ h1 => WP.mono (key_call (init_kc h0' h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
  have c := rel_agree (F := IS2 s₀) (F' := IS2 s₀') (G := IS3 s₀) (G' := IS3 s₀') (c := .block initArgs)
    (Taint.ofRegs [.r8, .r9, .r11])
    (fun s s' e e' => by
      obtain ⟨g9, g11, g8, -⟩ := e.g
      obtain ⟨g9', g11', g8', -⟩ := e'.g
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g8, g8', q₂]
      · rw [g9, g9', q₃]
      · rw [g11, g11', q₄]) ⟨_, by taint_decide⟩
    (fun s e => by obtain ⟨s₃, run⟩ := is3_run h0 e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
    (fun s e => by obtain ⟨s₃, run⟩ := is3_run h0' e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
  have d := rel_wp (F := IS3 s₀) (F' := IS3 s₀') (G := IS4 s₀) (G' := IS4 s₀')
    (ctr_rel fun s₁ s₂ h => ⟨_, _, _, _, _, _, init_cc h0 h.1,
      by have := init_cc h0' h.2; rwa [← q₃, ← q₄, eR] at this,
      by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e⟩ := h.1.facts h0
         obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e'⟩ := h.2.facts h0'
         rw [e, e', q₀]⟩)
    (fun s₃ h3 => WP.mono (ctr_call (init_cc h0 h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
    (fun s₃ h3 => WP.mono (ctr_call (init_cc h0' h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => IS4 s₀ s₁ ∧ IS4 s₀' s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r11 h0, h.2.r11 h0', q₄]) hB
  exact a.seq (b.seq (c.seq (d.seq e)))

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

end

/-!
# AES-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with 8 bytes of stack: each call of
`vg_aes_ctr32` or `vg_ghash` pushes two words.
-/

@[expose] public section

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

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

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Proof.AesGcm.initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, initArm, bel, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat, mkSat] using initSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamInit_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamInit (Proof.AesGcm.streamInitScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamInit_wp hs) streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, streamInitArm, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamAad_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamAad (Proof.AesGcm.streamAadScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamAad_wp hs) streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, streamAadArm, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using saSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamEncrypt_wp hs) streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, streamEncryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamDecrypt_wp hs) streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, streamDecryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

/-- `mkSat`, with the stack argument 4 (at `0x8010`) `0x4000`. -/
def mkSat4 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { mkSat g rd wr with mem := fun a => if a = 0x8011 then 0x40 else 0 }

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition (with `tag` at `0x4000` and `work`
at 0). -/
def fSat : State :=
  mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩, ⟨0, 2560⟩]

theorem streamFinish_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamFinish (Proof.AesGcm.streamFinishScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamFinish_wp hs) streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Proof.AesGcm.streamFinishRoundsPost, streamFinishArm, streamFinishPreArm, finPub, bel, arg,
      args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using fSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def vSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target streamVerify (Proof.AesGcm.streamVerifyScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamVerify_wp hs) streamVerify_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPre, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args, arg64, roundsOk,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Proof.AesGcm.streamVerifyRoundsPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [streamVerifyArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _ iv a c hs ha hc
        rw [e]
        exact h iv a c hs ha hc
      pub := by
        sig_implies_pub [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPre, streamVerifyArm, streamVerifyPreArm, finPub, bel, arg, args, arg64, roundsOk,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using vSat }

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or
data, `tag` at `0x4000` and `work` at 0). -/
def oSat : State :=
  mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0, 2560⟩]

theorem seal_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «seal» (Proof.AesGcm.sealScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealArm, sealPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using oSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data, data
or tag, and `work` at 0). -/
def opSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0, 0⟩, ⟨0, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «open» (Proof.AesGcm.openScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, openArm,
          openPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Proof.AesGcm.openRoundsPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openArm,
          openPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
          · exact a3
          · exact a4
          · exact a5
          · exact a6
        · have e₁ : ¬((s₁.gpr .r1).toNat = 10 ∨ (s₁.gpr .r1).toNat = 12 ∨ (s₁.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .r1).toNat = 10 ∨ (s₂.gpr .r1).toNat = 12 ∨ (s₂.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x (h1 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, openArm,
          openPreArm, onePub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using opSat }

end VG.Proof.AesGcm.Arm
