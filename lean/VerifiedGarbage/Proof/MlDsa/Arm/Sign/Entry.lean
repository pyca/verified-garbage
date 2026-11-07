module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inv
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Correct
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

/-!
# ML-DSA signing on ARMv7: the entries of the kernel

`vg_mldsa*_sign_with_cache` (`withCache`) is the kernel of `vg_mldsa*_sign`
and of the prepared keys' `vg_mldsa*_sign_prepared` (`signEntry`), which call
it with no prepared polynomials (`cache = 0`) and with those after the encoded
key, in a frame saving `r4` and `lr`, with `lr` kept in `r4` across the call,
and `scratch` and `cache` pushed as its arguments on the stack: 16 bytes of
stack above the kernel's 28.

The entries are verified against `signE`: `signK` without `cache`, for an
encoded key (`prepared` false) or a prepared private key (`prepared` true).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Proof.MlDsa.Message (Within within_off within_base within_self)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Memory kept -/

/-- A prepared private key is kept by a frame apart from it. -/
theorem prepared_keep {p : Params} {m m' : Mem} {W : List Region} {key : Addr} (hf : Frame W m m')
    (hd : ∀ R ∈ W, (⟨key, preparedSecretKeyBytes p⟩ : Region).Disjoint R) (hb : preparedSecretKeyBytes p ≤ 2 ^ 64)
    (h : PreparedSecretKey p m key) : PreparedSecretKey p m' key := by
  have h256 : n = 256 := rfl
  have hsk : bytesAt m' key p.skLen = bytesAt m key p.skLen :=
    VG.Proof.MlKem.bytesAt_frame hf (fun R hR => (hd R hR).sub_left (Region.sub_prefix (by
      simp only [preparedSecretKeyBytes]; omega))) (by simp only [preparedSecretKeyBytes] at hb; omega)
  intro i hi j hj
  rw [hsk, ← h i hi j hj]
  have hsub : Region.Sub ⟨key + BitVec.ofNat 64 (p.skLen + 4 * n * i) + BitVec.ofNat 64 (4 * j), 4⟩
      ⟨key, preparedSecretKeyBytes p⟩ := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine Offset.sub_base key ?_
    rw [h256] at hj ⊢
    simp only [preparedSecretKeyBytes, h256]
    omega
  exact congrArg BitVec.toNat (hf.readW (Region.contains_self _ _) (fun R hR => (hd R hR).sub_left hsub) (by decide))

/-! ## Before the call -/

/-- The state the kernel is called from, after the push of `σ`'s `r4` and
`lr`: `lr` kept in `r4`, `scratch` in `r12` and `cache` in `lr`. -/
structure Mid (p : Params) (prepared : Bool) (σ s : State) : Prop where
  gpr : ∀ r, r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s.gpr r = σ.gpr r
  r4 : s.gpr .r4 = σ.gpr .lr
  r12 : s.gpr .r12 = stackArg σ 0
  lr : s.gpr .lr = cacheV p prepared (σ.gpr .r0)
  sp : s.sp = σ.sp - BitVec.ofNat 32 8
  mem : s.mem = (pushed [.r4, .lr] σ).mem
  rd : s.rd = σ.rd
  wr : s.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 8), 8⟩ :: σ.wr

theorem blockA_ok {p : Params} {prepared : Bool} {D : Nat} {σ : State} (hpre : (signE p prepared D).pre σ)
    (hD : 8 ≤ D) :
    WP isa (.block (([.ldrSp .r12 8, .mov .r4 (.reg .lr)] : List Instr) ++ setCache p prepared))
      (pushed [.r4, .lr] σ) (Mid p prepared σ) := by
  have hpre' := hpre
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp, hsp4, -⟩ := hpre'
  have h8 : 8 ≤ σ.sp.toNat := by omega
  rw [WP.block_append_iff]
  have esp : (pushed [.r4, .lr] σ).sp + BitVec.ofNat 32 8 = σ.sp := by
    rw [pushed_sp]; exact BitVec.sub_add_cancel _ _
  have hA : InRegions ((pushed [.r4, .lr] σ).rd ++ (pushed [.r4, .lr] σ).wr)
      (State.addr ((pushed [.r4, .lr] σ).sp + BitVec.ofNat 32 8)) 4 := by
    rw [esp, pushed_rd]
    refine ⟨⟨stackArgAddr σ 0, 4⟩, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    simp [stackArgAddr, Region.Contains]
  have h8' : (8 : Nat) < 4096 := by decide
  have hl : WP isa (.block [.ldrSp .r12 8, .mov .r4 (.reg .lr)]) (pushed [.r4, .lr] σ) fun s =>
      s.gpr .r12 = (pushed [.r4, .lr] σ).mem.readW (State.addr σ.sp) 32 ∧ s.gpr .r4 = σ.gpr .lr ∧
      (∀ r, r ≠ .r12 → r ≠ .r4 → s.gpr r = σ.gpr r) ∧ s.mem = (pushed [.r4, .lr] σ).mem ∧
      s.rd = σ.rd ∧ s.wr = (pushed [.r4, .lr] σ).wr ∧ s.sp = σ.sp - BitVec.ofNat 32 8 := by
    run_block [hA, h8']
    exact ⟨by rw [esp], rfl, fun r h12 h4 => by simp [h12, h4], trivial, rfl, trivial, rfl⟩
  refine WP.mono hl fun s₁ ⟨g12, g4, g, gm, grd, gwr, gsp⟩ => ?_
  have e12 : s₁.gpr .r12 = stackArg σ 0 := by
    rw [g12, stackArg, stackArgAddr, show 4 * 0 = 0 from rfl, BitVec.add_zero]
    refine (Argon2.Arm.pushed_stk (rs := [.r4, .lr]) (s := σ) (by simp only [List.length_cons, List.length_nil]; omega)).readW
      (Region.contains_self _ _) (fun R hR => ?_) (by decide)
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.base_disjoint_below _ (by simp only [List.length_cons, List.length_nil]; omega)
  have fin : ∀ s, s.gpr .lr = cacheV p prepared (σ.gpr .r0) → Keep [.lr] s₁ s → Mid p prepared σ s :=
    fun s hl k => ⟨fun r h4 h12 hl' => by rw [k.gpr r (by simpa using hl'), g r h12 h4],
      by rw [k.gpr _ (by decide), g4], by rw [k.gpr _ (by decide), e12], hl, by rw [k.sp, gsp],
      by rw [k.mem, gm], by rw [k.rd, grd], by rw [k.wr, gwr, pushed_wr]; rfl⟩
  cases prepared
  · exact WP.mono (movi_ok .lr 0 s₁) fun s ⟨hv, k⟩ => fin s (by rw [hv]; rfl) k
  · exact WP.mono (lea_ok .lr (.r0, p.skLen) (show Reg.r0 ≠ Reg.lr by decide) s₁) fun s ⟨hv, k⟩ => fin s
      (by rw [hv, g .r0 (by decide) (by decide)]; rfl) k

/-! ## The call -/

/-- The regions the kernel reads: the encoded key, `μ`, `rnd`, its arguments
and the prepared polynomials. -/
def kRd (p : Params) (prepared : Bool) (σ : State) : List Region :=
  ⟨State.addr (σ.gpr .r0), p.skLen⟩ :: ⟨State.addr (σ.gpr .r1), 64⟩ :: ⟨State.addr (σ.gpr .r2), 32⟩ ::
    belowA (σ.sp - BitVec.ofNat 32 8) 8 ::
    (if cacheV p prepared (σ.gpr .r0) = 0 then [] else
      [⟨State.addr (cacheV p prepared (σ.gpr .r0)), cacheLen p⟩])

/-- The state the kernel is entered in. -/
abbrev kE (p : Params) (prepared : Bool) (σ s : State) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions (kRd p prepared σ) σ.wr

theorem belowA_eq (sp : BitVec 32) (n : Nat) : belowA sp n = Argon2.Arm.stkR sp n := rfl

/-- The stack the entry uses, below `σ`'s stack pointer, holds the frames and the kernel's. -/
theorem sub_args {sp : BitVec 32} (h : entryStack ≤ sp.toNat) :
    Region.Sub (belowA (sp - BitVec.ofNat 32 8) 8) (belowA sp entryStack) := by
  rw [belowA_eq, belowA_eq]; exact Argon2.Arm.stkR_inner (by decide) h

theorem sub_kern {sp : BitVec 32} (h : entryStack ≤ sp.toNat) :
    Region.Sub (belowA (sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8) signStack) (belowA sp entryStack) := by
  rw [belowA_eq, belowA_eq]
  have h8 : 8 ≤ sp.toNat := by simp only [entryStack] at h; omega
  exact fun x hx => Argon2.Arm.stkR_inner (sp := sp) (a := 36) (k := 8) (b := entryStack) (by decide) h x
    (Argon2.Arm.stkR_inner (sp := sp - BitVec.ofNat 32 8) (a := signStack) (k := 8) (b := 36) (by decide)
      (by rw [FrameStack.sub_toNat' h8]; simp only [entryStack] at h; omega) x hx)

theorem sub_frames {sp : BitVec 32} (h : entryStack ≤ sp.toNat) :
    Region.Sub (Argon2.Arm.stkR sp 16) (belowA sp entryStack) := by
  rw [belowA_eq]; exact Argon2.Arm.stkR_sub (by decide) h

section
variable {p : Params} {prepared : Bool} {σ s : State} (hpre : (signE p prepared entryStack).pre σ)
  (hm : Mid p prepared σ s)
include hpre hm

omit hpre in
theorem kE_gpr {r : Reg} (hr : r ∉ linkRegs) (h4 : r ≠ .r4) (h12 : r ≠ .r12) (hl : r ≠ .lr) :
    (kE p prepared σ s).gpr r = σ.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr, hm.gpr r h4 h12 hl]

theorem kE_sp8 : 8 ≤ s.sp.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp, -⟩ := hpre
  rw [hm.sp, FrameStack.sub_toNat' (by simp only [entryStack] at hsp; omega)]
  simp only [entryStack] at hsp; omega

theorem kE_arg0 : stackArg (kE p prepared σ s) 0 = stackArg σ 0 := by
  rw [Argon2.Arm.pushed_arg (by simp only [List.length_cons, List.length_nil]; have := kE_sp8 hpre hm; omega)
    (by decide)]
  exact hm.r12

theorem kE_arg1 : stackArg (kE p prepared σ s) 1 = cacheV p prepared (σ.gpr .r0) := by
  rw [Argon2.Arm.pushed_arg (by simp only [List.length_cons, List.length_nil]; have := kE_sp8 hpre hm; omega)
    (by decide)]
  exact hm.lr

theorem kE_argAddr : stackArgAddr (kE p prepared σ s) 0 = (belowA (σ.sp - BitVec.ofNat 32 8) 8).base := by
  rw [Argon2.Arm.pushed_argAddr (by simp only [List.length_cons, List.length_nil]; have := kE_sp8 hpre hm; omega),
    hm.sp]
  rfl

omit hpre in
theorem kE_sp : (kE p prepared σ s).sp = σ.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, hm.sp]; rfl

/-- The pushes keep memory but within 16 bytes below `σ`'s stack pointer. -/
theorem kE_mem : Frame [Argon2.Arm.stkR σ.sp 16] σ.mem (kE p prepared σ s).mem := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp, -⟩ := hpre'
  have h8 := kE_sp8 hpre hm
  have hσ : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hsp; omega
  simp only [State.withRegions_mem, State.callEntry_mem]
  have f₁ := Argon2.Arm.pushed_stk (rs := [.r4, .lr]) (s := σ) (by simp only [List.length_cons, List.length_nil]; omega)
  have f₂ := Argon2.Arm.pushed_stk (rs := [.r12, .lr]) (s := s) (by simp only [List.length_cons, List.length_nil]; omega)
  rw [hm.mem] at f₂
  rw [hm.sp] at f₂
  refine Frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
  · simp only [List.mem_singleton] at hr; subst hr; exact Argon2.Arm.stkR_sub (by decide) hσ
  · simp only [List.mem_singleton] at hr; subst hr
    exact Argon2.Arm.stkR_inner (by decide) hσ

/-- The kernel's precondition, on entry to it. -/
theorem kE_pre (hc : 0 < cacheLen p) : (signK p signStack).pre (kE p prepared σ s) := by
  have hpre' := hpre
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp, hsp4, hq⟩ :=
    hpre'
  have e0 := kE_gpr hm (r := .r0) (by decide) (by decide) (by decide) (by decide)
  have e1 := kE_gpr hm (r := .r1) (by decide) (by decide) (by decide) (by decide)
  have e2 := kE_gpr hm (r := .r2) (by decide) (by decide) (by decide) (by decide)
  have e3 := kE_gpr hm (r := .r3) (by decide) (by decide) (by decide) (by decide)
  have ea0 := kE_arg0 hpre hm
  have ea1 := kE_arg1 hpre hm
  have eaa := kE_argAddr hpre hm
  have esp := kE_sp hm
  have hσ : entryStack ≤ σ.sp.toNat := hsp
  have h16 : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hσ; omega
  have keySub : Region.Sub ⟨State.addr (σ.gpr .r0), p.skLen⟩ ⟨State.addr (σ.gpr .r0), secretKeyLen p prepared⟩ :=
    Region.sub_prefix (by have := secretKeyLen_ge p prepared; omega)
  have kS := sub_kern hσ
  have aS := sub_args hσ
  have espN : (σ.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8).toNat = σ.sp.toNat - 16 := by
    rw [FrameStack.sub_toNat' (by rw [FrameStack.sub_toNat' (by omega)]; omega), FrameStack.sub_toNat' (by omega)]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [e0, e1, e2, e3, ea0, esp]
  · rw [State.withRegions_rd]
    simp only [kRd, cacheRd, cacheR, eaa, ea1]
    rfl
  · rw [State.withRegions_wr]; exact hwr
  · exact d1.sub_left keySub
  · exact d2.sub_left keySub
  · exact d3
  · exact d4
  · exact d5
  · exact d6
  · exact d7
  · rw [eaa]; exact k4.symm.sub_right aS
  · rw [eaa]; exact k5.symm.sub_right aS
  · exact (k1.sub_left kS).sub_right keySub
  · exact k2.sub_left kS
  · exact k3.sub_left kS
  · exact k4.sub_left kS
  · exact k5.sub_left kS
  · have := secretKeyLen_ge p prepared; omega
  · exact n2
  · exact n3
  · exact n4
  · exact n5
  · rw [espN]; simp only [entryStack, signStack] at hσ ⊢; omega
  · rw [espN]; omega
  · intro hne
    simp only [cacheR, ea1, e0, e3, ea0, esp] at hne ⊢
    cases prepared
    · exact absurd rfl hne
    have hk : secretKeyLen p true = p.skLen + cacheLen p := by
      simp only [secretKeyLen, preparedSecretKeyBytes, cacheLen, n, ite_true]
    have ec : State.addr (σ.gpr .r0 + BitVec.ofNat 32 p.skLen) =
        State.addr (σ.gpr .r0) + BitVec.ofNat 64 p.skLen := addr_add (by rw [hk] at n1; omega)
    have cS : Region.Sub ⟨State.addr (σ.gpr .r0) + BitVec.ofNat 64 p.skLen, cacheLen p⟩
        ⟨State.addr (σ.gpr .r0), secretKeyLen p true⟩ := Offset.sub_base _ (by rw [hk])
    simp only [cacheV, ite_true, ec]
    refine ⟨d1.sub_left cS, d2.sub_left cS, (k1.sub_left kS).sub_right cS, ?_, fun i hi => ?_⟩
    · rw [hk] at n1
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.skLen) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega
    · have hb : preparedSecretKeyBytes p ≤ 2 ^ 64 := by
        have : secretKeyLen p true = preparedSecretKeyBytes p := rfl
        omega
      have hP := prepared_keep (kE_mem hpre hm) (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        exact (k1.symm.sub_right (sub_frames hσ))) hb (hq rfl)
      have := (preparedSecretKey_iff.mp hP) i hi
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact this

/-- The regions the kernel is given are the entry's, and its arguments. -/
theorem kE_covers (hc : 0 < cacheLen p) : Covers (kRd p prepared σ ++ σ.wr) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) ∧
    Covers σ.wr (pushed [.r12, .lr] s).wr := by
  have hpre' := hpre
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n1, -, -, -, -, hsp, -⟩ := hpre'
  have h8 : 8 ≤ (σ.sp - BitVec.ofNat 32 8).toNat := by
    rw [← hm.sp]; exact kE_sp8 hpre hm
  refine ⟨VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_,
    fun a n ⟨R, hR, hc⟩ => ⟨R, by rw [pushed_wr, hm.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR), hc⟩⟩
  simp only [pushed_rd, pushed_wr, hm.rd, hm.wr, hm.sp, hrd]
  simp only [kRd, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with rfl | rfl | rfl | rfl | hr | hr
  · exact ⟨⟨State.addr (σ.gpr .r0), secretKeyLen p prepared⟩, by simp, within_base _ (by have := secretKeyLen_ge p prepared; omega)⟩
  · exact ⟨_, by simp, within_self _⟩
  · exact ⟨_, by simp, within_self _⟩
  · refine ⟨⟨State.addr (σ.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8), 8⟩, by simp, ?_⟩
    show Within ⟨State.addr (σ.sp - BitVec.ofNat 32 8) - BitVec.ofNat 64 8, 8⟩ _
    rw [FrameStack.addr_sub' h8]; exact within_self _
  · cases prepared
    · simp [cacheV] at hr
    · have hk : secretKeyLen p true = p.skLen + cacheLen p := by
        simp only [secretKeyLen, preparedSecretKeyBytes, cacheLen, n, ite_true]
      simp only [cacheV, ite_true, List.mem_ite_nil_left, List.mem_singleton] at hr
      obtain ⟨-, rfl⟩ := hr
      refine ⟨⟨State.addr (σ.gpr .r0), secretKeyLen p true⟩, by simp, ?_⟩
      rw [hk] at n1
      have hlt : (σ.gpr .r0).toNat + p.skLen < 2 ^ 32 := by omega
      have ec : State.addr (σ.gpr .r0 + BitVec.ofNat 32 p.skLen) =
          State.addr (σ.gpr .r0) + BitVec.ofNat 64 p.skLen := addr_add hlt
      rw [ec]; exact within_off _ (by rw [hk])
  · exact ⟨r, by simp [hr], within_self _⟩

/-- The kernel sees the entry's key, `μ` and `rnd`. -/
theorem kE_bytes {a : Addr} {len : Nat} (hd : (belowA σ.sp entryStack).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt (kE p prepared σ s).mem a len = bytesAt σ.mem a len := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp, -⟩ := hpre'
  exact VG.Proof.MlKem.bytesAt_frame (kE_mem hpre hm) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR; exact (hd.symm.sub_right (sub_frames hsp))) hl

end

/-! ## The entries -/

theorem withCache_stack {p : Params} (h3 : Ok3 p) : FrameStack.armStack (withCache prims p) ≤ signStack := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem cacheLen_pos {p : Params} (h3 : Ok3 p) : 0 < cacheLen p := by
  rcases h3 with rfl | rfl | rfl <;> decide

/-- The word `r4` was pushed to, by the entry's frame, is kept by the call. -/
theorem r4_kept {p : Params} {prepared : Bool} {σ s s₃ : State} (hpre : (signE p prepared entryStack).pre σ)
    (hm : Mid p prepared σ s) (hf : Frame (σ.wr ++ [Argon2.Arm.stkR s.sp 36]) s.mem s₃.mem) :
    s₃.mem.readW (State.addr (σ.sp - BitVec.ofNat 32 8)) 32 = σ.gpr .r4 := by
  have hpre' := hpre
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, k4, k5, -, -, -, -, -, hsp, -⟩ := hpre'
  have h16 : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hsp; omega
  have h8 : 8 ≤ σ.sp.toNat := by omega
  have hsub : Region.Sub ⟨State.addr (σ.sp - BitVec.ofNat 32 8), 4⟩ (belowA σ.sp entryStack) := by
    refine fun x hx => (Argon2.Arm.stkR_sub (a := 8) (b := entryStack) (by decide) hsp) x ?_
    rw [FrameStack.addr_sub' h8] at hx
    have := Offset.sub_base (State.addr σ.sp - BitVec.ofNat 64 8) (d := 0) (n := 4) (k := 8) (by omega) x
      (by simpa using hx)
    exact this
  rw [hf.readW (Region.contains_self _ _) ?_ (by decide), hm.mem]
  · have := Argon2.Arm.storeWords_readW σ.mem (σ.sp - BitVec.ofNat 32 8) [σ.gpr .r4, σ.gpr .lr]
      (by rw [FrameStack.sub_toNat' h8]; have := σ.sp.isLt; simp; omega) (i := 0) (by simp)
    simpa [pushed] using this
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact k4.sub_left hsub
      · exact k5.sub_left hsub
    · rw [List.mem_singleton] at hr; subst hr
      rw [hm.sp]
      show Region.Disjoint ⟨State.addr (σ.sp - BitVec.ofNat 32 8), 4⟩
        ⟨State.addr (σ.sp - BitVec.ofNat 32 8) - BitVec.ofNat 64 36, 36⟩
      exact Offset.base_disjoint_below (State.addr (σ.sp - BitVec.ofNat 32 8)) (n := 36) (k := 4) (by omega)

theorem entry_correct {p : Params} (h3 : Ok3 p) (prepared : Bool) (σ : State)
    (hpre : (signE p prepared entryStack).pre σ) :
    ∃ t s', Exec isa (signEntry prims p prepared) σ t s' ∧ abiPreserved σ s' ∧
      (signE p prepared entryStack).post σ s' := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -, -, n1, -, -, -, -, hsp, -, -⟩ := hpre'
  have hσ : entryStack ≤ σ.sp.toNat := hsp
  have h16 : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hσ; omega
  unfold signEntry entry
  refine (WP.frame (rs := [.r4, .lr]) (r := .r4) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega) (by decide) ?_).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  refine WP.seq (WP.mono (blockA_ok hpre (by decide)) fun s₁ hm => ?_)
  have hc := cacheLen_pos h3
  have cov := kE_covers hpre hm hc
  refine WP.seq (Argon2.Arm.frameCall_ok (rs := [.r12, .lr]) (t := .r12) (by decide) (by decide) (by decide)
    (sign_correct prims_ok h3) (K := 36) (by have := withCache_stack h3; simp only [List.length_cons,
      List.length_nil, signStack] at this ⊢; omega)
    (by rw [hm.sp, FrameStack.sub_toNat' (by omega)]; simp only [entryStack] at hσ; omega)
    (kE_pre hpre hm hc) cov.1 cov.2 fun s₂ hA hpost => ?_)
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ₄ u₄ => WP.block_nil ?_
  have r4' : σ₄.gpr .lr = σ.gpr .lr := by rw [u₄.gpr, hA.cs .r4 (by decide) (by decide), hm.r4]
  have sp4 : σ₄.sp = σ.sp - BitVec.ofNat 32 8 := by rw [u₄.sp, hA.sp, hm.sp]
  have hw4 : σ₄.mem.readW (State.addr σ₄.sp) 32 = σ.gpr .r4 := by
    rw [sp4, u₄.mem]; exact r4_kept hpre hm hA.frame
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4
      show (σ₄.setReg .r4 (σ₄.mem.readW (State.addr σ₄.sp) 32)).gpr .r4 = _
      rw [RegUpd.gpr_setReg_self]; exact hw4
    · rw [popped_gpr h4]
      by_cases hl : r = .lr
      · subst hl; exact r4'
      · have h12 : r ≠ .r12 := by rintro rfl; revert hr; decide
        rw [u₄.other r hl, hA.cs r hr hl, hm.gpr r h4 h12 hl]
  · rw [popped_sp, sp4]; exact BitVec.sub_add_cancel _ _
  · have e0 := kE_gpr hm (r := .r0) (by decide) (by decide) (by decide) (by decide)
    have e1 := kE_gpr hm (r := .r1) (by decide) (by decide) (by decide) (by decide)
    have e2 := kE_gpr hm (r := .r2) (by decide) (by decide) (by decide) (by decide)
    have e3 := kE_gpr hm (r := .r3) (by decide) (by decide) (by decide) (by decide)
    have keySub : Region.Sub ⟨State.addr (σ.gpr .r0), p.skLen⟩ ⟨State.addr (σ.gpr .r0), secretKeyLen p prepared⟩ :=
      Region.sub_prefix (by have := secretKeyLen_ge p prepared; omega)
    have b0 : bytesAt (pushed [.r12, .lr] s₁).mem _ _ = _ :=
      kE_bytes hpre hm (k1.sub_right keySub) (by have := secretKeyLen_ge p prepared; omega)
    have b1 : bytesAt (pushed [.r12, .lr] s₁).mem _ _ = _ := kE_bytes hpre hm k2 (by decide)
    have b2 : bytesAt (pushed [.r12, .lr] s₁).mem _ _ = _ := kE_bytes hpre hm k3 (by decide)
    show Outcome _ _ _
    have hpost' : Outcome _ _ _ := hpost
    simp only [State.withRegions_gpr, e0, e1, e2, e3] at hpost'
    simp only [State.withRegions_mem, State.callEntry_mem, b0, b1, b2] at hpost'
    have g0 : (popped .r4 (4 * [Reg.r4, .lr].length) σ₄).gpr .r0 = s₂.gpr .r0 := by
      rw [popped_gpr (by decide), u₄.other _ (by decide), popped_gpr (by decide)]
    rw [g0, popped_mem, u₄.mem, popped_mem]
    exact hpost'

/-! ## Constant time -/

theorem setCache_nomem (p : Params) (prepared : Bool) :
    ∀ i ∈ (.mov .r4 (.reg .lr) :: setCache p prepared : List Instr), ∀ s, isa.addrs i s = [] := by
  intro i hi s
  cases prepared <;>
    simp only [setCache, lea, movi, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl | rfl | rfl <;> rfl

/-- The moves before the call leak only the stack pointer. -/
theorem blockA_tr {p : Params} {prepared : Bool} {P : State → State → Prop} (hP : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block (([.ldrSp .r12 8, .mov .r4 (.reg .lr)] : List Instr) ++ setCache p prepared))
      fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff, show (([.ldrSp .r12 8, .mov .r4 (.reg .lr)] : List Instr) ++ setCache p prepared) =
    [.ldrSp .r12 8] ++ (.mov .r4 (.reg .lr) :: setCache p prepared) from rfl, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, a₁⟩, h₁, g₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, a₂⟩, h₂, g₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨v₁, b₁⟩, f₁, k₁⟩ := Option.map_eq_some_iff.mp g₁
  obtain ⟨⟨v₂, b₂⟩, f₂, k₂⟩ := Option.map_eq_some_iff.mp g₂
  simp only [Prod.mk.injEq] at k₁ k₂
  refine ⟨?_, trivial⟩
  rw [← k₁.2, ← k₂.2, ldrSp_leak h₁, ldrSp_leak h₂, execBlock_nomem (setCache_nomem p prepared) f₁,
    execBlock_nomem (setCache_nomem p prepared) f₂, hP _ _ hp]

theorem entry_ct {p : Params} (h3 : Ok3 p) (prepared : Bool) :
    ConstantTime isa (signE p prepared entryStack).pre (signE p prepared entryStack).pub
      (signEntry prims p prepared) := by
  unfold signEntry entry
  refine RelCT.constantTime (RelCT.frame (fun s₁ s₂ h => h.2.2.2.2.2.2.2.1) ?_)
  refine RelCT.mono (P := fun a b => ∃ q : State × State, ((signE p prepared entryStack).pre q.1 ∧
      (signE p prepared entryStack).pre q.2 ∧ (signE p prepared entryStack).pub q.1 q.2) ∧
      a = pushed [.r4, .lr] q.1 ∧ b = pushed [.r4, .lr] q.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨σ₁, σ₂⟩ => ?_
  refine RelCT.seq (RelCT.wp (F₁ := fun s => ((signE p prepared entryStack).pre σ₁ ∧
      (signE p prepared entryStack).pre σ₂ ∧ (signE p prepared entryStack).pub σ₁ σ₂) ∧ Mid p prepared σ₁ s)
    (F₂ := Mid p prepared σ₂) (blockA_tr fun a b ⟨h, ha, hb⟩ => by
      rw [ha, hb, pushed_sp, pushed_sp, h.2.2.2.2.2.2.2.1])
    fun a b ⟨h, ha, hb⟩ => ⟨ha ▸ WP.mono (blockA_ok h.1 (by decide)) fun _ e => ⟨h, e⟩,
      hb ▸ blockA_ok h.2.1 (by decide)⟩) ?_
  have hc := cacheLen_pos h3
  refine RelCT.seq (Argon2.Arm.frameCall_rel (rs := [.r12, .lr]) (t := .r12) (by decide)
    (sign_correct prims_ok h3) (sign_ct prims_ok h3) (kRd p prepared σ₁) σ₁.wr
    fun x y ⟨_, ⟨⟨h₁, h₂, hp⟩, m₁⟩, m₂⟩ => ?_)
    (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
  obtain ⟨p0, p1, p2, p3, pa, psp, pl⟩ := hp
  have h₂' := h₂
  obtain ⟨-, hwr₂, -⟩ := h₂'
  have h₁' := h₁
  obtain ⟨-, hwr₁, -⟩ := h₁'
  have erd : kRd p prepared σ₂ = kRd p prepared σ₁ := by simp only [kRd, p0, p1, p2, psp]
  have ewr : σ₂.wr = σ₁.wr := by rw [hwr₁, hwr₂, p3, pa]
  have hEq : (pushed [.r12, .lr] y).callEntry.withRegions (kRd p prepared σ₁) σ₁.wr = kE p prepared σ₂ y := by
    simp only [kE, erd, ewr]
  have cov₂ := kE_covers h₂ m₂ hc
  rw [erd, ewr] at cov₂
  rw [hEq]
  refine ⟨by rw [m₁.sp, m₂.sp, psp], kE_pre h₁ m₁ hc, kE_pre h₂ m₂ hc, ?_, (kE_covers h₁ m₁ hc).1,
    (kE_covers h₁ m₁ hc).2, cov₂.1, cov₂.2⟩
  have g₁ : ∀ r, r ∉ linkRegs → r ≠ .r4 → r ≠ .r12 → r ≠ .lr →
      (kE p prepared σ₁ x).gpr r = σ₁.gpr r := fun r a b c d => kE_gpr m₁ a b c d
  have g₂ : ∀ r, r ∉ linkRegs → r ≠ .r4 → r ≠ .r12 → r ≠ .lr →
      (kE p prepared σ₂ y).gpr r = σ₂.gpr r := fun r a b c d => kE_gpr m₂ a b c d
  have keyB : ∀ (σ s : State), (signE p prepared entryStack).pre σ → Mid p prepared σ s →
      bytesAt (kE p prepared σ s).mem (State.addr (σ.gpr .r0)) p.skLen = bytesAt σ.mem (State.addr (σ.gpr .r0)) p.skLen ∧
      bytesAt (kE p prepared σ s).mem (State.addr (σ.gpr .r1)) 64 = bytesAt σ.mem (State.addr (σ.gpr .r1)) 64 ∧
      bytesAt (kE p prepared σ s).mem (State.addr (σ.gpr .r2)) 32 = bytesAt σ.mem (State.addr (σ.gpr .r2)) 32 :=
    fun σ s hpre hm => by
      have hpre' := hpre
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := hpre'
      exact ⟨kE_bytes hpre hm (k1.sub_right (Region.sub_prefix (by have := secretKeyLen_ge p prepared; omega)))
        (by have := secretKeyLen_ge p prepared; have := h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega),
        kE_bytes hpre hm k2 (by decide), kE_bytes hpre hm k3 (by decide)⟩
  obtain ⟨b₁0, b₁1, b₁2⟩ := keyB σ₁ x h₁ m₁
  obtain ⟨b₂0, b₂1, b₂2⟩ := keyB σ₂ y h₂ m₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), p0]
  · rw [g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), p1]
  · rw [g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), p2]
  · rw [g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), p3]
  · rw [kE_arg0 h₁ m₁, kE_arg0 h₂ m₂, pa]
  · rw [kE_sp m₁, kE_sp m₂, psp]
  · rw [g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide),
      b₁0, b₁1, b₁2, b₂0, b₂1, b₂2]
    exact pl
  · rw [kE_arg1 h₁ m₁, kE_arg1 h₂ m₂, p0]

end VG.Proof.MlDsa.Arm.Sign
