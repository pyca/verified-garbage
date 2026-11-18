module

public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTFn
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTJ0
import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTAbsorb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.CTCrypt
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Entry
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Flush
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Open
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Entry
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
meta import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

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
