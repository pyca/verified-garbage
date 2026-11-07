module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Layout
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call

/-!
# ML-DSA verification on 32-bit ARM: the entries of the kernel

`vg_mldsa*_verify_with_cache` (`withCache`) is the kernel of `vg_mldsa*_verify`
and of the prepared keys' `vg_mldsa*_verify_prepared` (`verifyEntry`), which
call it with no prepared polynomials (`cache = 0`) and with those after the
encoded key, in a frame saving `r4` and `lr`, with `lr` kept in `r4` across
the call, and `cache` pushed as its argument on the stack: 16 bytes of stack
above the kernel's 36.

The entries are verified against `verifyE`: `verifyK` without `cache`, for an
encoded key (`prepared` false) or a prepared public key (`prepared` true).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Impl.MlDsa.Arm.Verify
open VG.Proof.MlKem.Arm (regA below)
open VG.Proof.MlDsa.Arm.KeyGen (scrLen ldc_eq)
open VG.Proof.MlDsa.Message (Within within_off within_base within_self)
open VG.Proof.MlDsa.Arm.Sign (block_nomem_tr)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract of the entries -/

/-- The stack the kernel uses. -/
abbrev kernStack : Nat := 36

/-- The stack an entry uses: its frames (16 bytes), and the kernel's. -/
abbrev entryStack : Nat := 52

/-- The value of `cache` an entry passes. -/
def cacheV (p : Params) (prepared : Bool) (pk : BitVec 32) : BitVec 32 :=
  if prepared then pk + BitVec.ofNat 32 p.pkLen else 0

/-- The precondition of `vg_mldsa*_verify` or `vg_mldsa*_verify_prepared`
(`pk = r0, mu = r1, sig = r2, scratch = r3`) with `D` bytes of stack:
`verifyContract`'s, for a key of `publicKeyLen` bytes satisfying `PublicKeyOk`. -/
structure VE (p : Params) (prepared : Bool) (D : Nat) (s : State) : Prop where
  stk : D ≤ s.sp.toNat
  rd : s.rd = [regA (s.gpr .r0) (publicKeyLen p prepared), regA (s.gpr .r1) 64, regA (s.gpr .r2) p.sigLen]
  wr : s.wr = [regA (s.gpr .r3) (scrLen p)]
  d_pc : (regA (s.gpr .r0) (publicKeyLen p prepared)).Disjoint (regA (s.gpr .r3) (scrLen p))
  d_mc : (regA (s.gpr .r1) 64).Disjoint (regA (s.gpr .r3) (scrLen p))
  d_sc : (regA (s.gpr .r2) p.sigLen).Disjoint (regA (s.gpr .r3) (scrLen p))
  b_p : (below s D).Disjoint (regA (s.gpr .r0) (publicKeyLen p prepared))
  b_m : (below s D).Disjoint (regA (s.gpr .r1) 64)
  b_s : (below s D).Disjoint (regA (s.gpr .r2) p.sigLen)
  b_c : (below s D).Disjoint (regA (s.gpr .r3) (scrLen p))
  f_p : (s.gpr .r0).toNat + publicKeyLen p prepared ≤ 2 ^ 32
  f_m : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  f_s : (s.gpr .r2).toNat + p.sigLen ≤ 2 ^ 32
  f_c : (s.gpr .r3).toNat + scrLen p ≤ 2 ^ 32
  key : PublicKeyOk p prepared s.mem (State.addr (s.gpr .r0))

/-- `vg_mldsa*_verify` or `vg_mldsa*_verify_prepared` with `D` bytes of stack:
`VE`, `verifyContract`'s result, and its public data. -/
def verifyE (p : Params) (prepared : Bool) (D : Nat) : Contract isa where
  pre := VE p prepared D
  post := (verifyK p kernStack).post
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ pkOf p s₁ = pkOf p s₂ ∧ muOf s₁ = muOf s₂ ∧ sgOf p s₁ = sgOf p s₂

theorem publicKeyLen_eq (p : Params) (prepared : Bool) :
    publicKeyLen p prepared = p.pkLen + (if prepared then 1024 * p.k else 0) := by
  cases prepared <;> simp [publicKeyLen, preparedPublicKeyBytes, n]

/-! ## Before the call -/

/-- The state the kernel is called from, after the push of `σ`'s `r4` and
`lr`: `lr` kept in `r4`, and `cache` in `r12`. -/
structure Mid (p : Params) (prepared : Bool) (σ s : State) : Prop where
  gpr : ∀ r, r ≠ .r4 → r ≠ .r12 → s.gpr r = σ.gpr r
  r4 : s.gpr .r4 = σ.gpr .lr
  r12 : s.gpr .r12 = cacheV p prepared (σ.gpr .r0)
  sp : s.sp = σ.sp - BitVec.ofNat 32 8
  mem : s.mem = (pushed [.r4, .lr] σ).mem
  rd : s.rd = σ.rd
  wr : s.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 8), 8⟩ :: σ.wr

theorem setC_ok (p : Params) (prepared : Bool) (s : State) :
    WP isa (.block (([.mov .r4 (.reg .lr)] : List Instr) ++ setCache p prepared)) s fun s' =>
      s'.gpr .r4 = s.gpr .lr ∧ s'.gpr .r12 = cacheV p prepared (s.gpr .r0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have hz : (0#16 ++ BitVec.extractLsb' 0 16 (BitVec.setWidth 32 0#16) : BitVec 32) = 0 := by decide
  apply WP.of_runBlock
  cases prepared <;>
    simp only [setCache, ↓reduceIte, reduceCtorEq, hz, and_self, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
      Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.sp_setReg, ldc_eq, cacheV] <;>
    exact ⟨trivial, trivial, fun r h4 h12 => by simp only [h4, h12, ite_false], trivial⟩

theorem blockA_ok (p : Params) (prepared : Bool) (σ : State) :
    WP isa (.block (([.mov .r4 (.reg .lr)] : List Instr) ++ setCache p prepared)) (pushed [.r4, .lr] σ)
      (Mid p prepared σ) :=
  WP.mono (setC_ok p prepared _) fun _ ⟨g4, g12, g, gm, grd, gwr, gsp⟩ =>
    ⟨fun r h4 h12 => by rw [g r h4 h12, pushed_gpr], by rw [g4, pushed_gpr], by rw [g12, pushed_gpr],
      by rw [gsp, pushed_sp]; rfl, gm, by rw [grd, pushed_rd], by rw [gwr, pushed_wr]; rfl⟩

/-! ## The call -/

/-- The regions the kernel reads: the encoded key, `μ`, the signature, its
argument and the prepared polynomials. -/
def kRd (p : Params) (prepared : Bool) (σ : State) : List Region :=
  [regA (σ.gpr .r0) p.pkLen, regA (σ.gpr .r1) 64, regA (σ.gpr .r2) p.sigLen,
    ⟨(belowA (σ.sp - BitVec.ofNat 32 8) 8).base, 4⟩] ++
    (if cacheV p prepared (σ.gpr .r0) = 0 then [] else
      [⟨State.addr (cacheV p prepared (σ.gpr .r0)), 1024 * p.k⟩])

/-- The state the kernel is entered in. -/
abbrev kE (p : Params) (prepared : Bool) (σ s : State) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions (kRd p prepared σ) σ.wr

theorem belowA_eq (sp : BitVec 32) (n : Nat) : belowA sp n = Argon2.Arm.stkR sp n := rfl

theorem sub_args {sp : BitVec 32} (h : entryStack ≤ sp.toNat) :
    Region.Sub (belowA (sp - BitVec.ofNat 32 8) 8) (belowA sp entryStack) := by
  rw [belowA_eq, belowA_eq]; exact Argon2.Arm.stkR_inner (by decide) h

theorem sub_kern {sp : BitVec 32} (h : entryStack ≤ sp.toNat) :
    Region.Sub (belowA (sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8) kernStack) (belowA sp entryStack) := by
  rw [belowA_eq, belowA_eq]
  have h8 : 8 ≤ sp.toNat := by simp only [entryStack] at h; omega
  exact fun x hx => Argon2.Arm.stkR_inner (sp := sp) (a := 44) (k := 8) (b := entryStack) (by decide) h x
    (Argon2.Arm.stkR_inner (sp := sp - BitVec.ofNat 32 8) (a := kernStack) (k := 8) (b := 44) (by decide)
      (by rw [FrameStack.sub_toNat' h8]; simp only [entryStack] at h; omega) x hx)

theorem sub_frames {sp : BitVec 32} (h : entryStack ≤ sp.toNat) :
    Region.Sub (Argon2.Arm.stkR sp 16) (belowA sp entryStack) := by
  rw [belowA_eq]; exact Argon2.Arm.stkR_sub (by decide) h

section
variable {p : Params} {prepared : Bool} {σ s : State} (hpre : VE p prepared entryStack σ)
  (hm : Mid p prepared σ s)
include hpre hm

omit hpre in
theorem kE_gpr {r : Reg} (hr : r ∉ linkRegs) (h4 : r ≠ .r4) (h12 : r ≠ .r12) :
    (kE p prepared σ s).gpr r = σ.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr, hm.gpr r h4 h12]

theorem kE_sp8 : 8 ≤ s.sp.toNat := by
  have hsp := hpre.stk
  rw [hm.sp, FrameStack.sub_toNat' (by simp only [entryStack] at hsp; omega)]
  simp only [entryStack] at hsp; omega

theorem kE_arg0 : stackArg (kE p prepared σ s) 0 = cacheV p prepared (σ.gpr .r0) := by
  rw [Argon2.Arm.pushed_arg (by simp only [List.length_cons, List.length_nil]; have := kE_sp8 hpre hm; omega)
    (by decide)]
  exact hm.r12

theorem kE_argAddr : stackArgAddr (kE p prepared σ s) 0 = (belowA (σ.sp - BitVec.ofNat 32 8) 8).base := by
  rw [Argon2.Arm.pushed_argAddr (by simp only [List.length_cons, List.length_nil]; have := kE_sp8 hpre hm; omega),
    hm.sp]
  rfl

omit hpre in
theorem kE_sp : (kE p prepared σ s).sp = σ.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, hm.sp]; rfl

/-- The pushes keep memory but within 16 bytes below `σ`'s stack pointer. -/
theorem kE_mem : Frame [Argon2.Arm.stkR σ.sp 16] σ.mem (kE p prepared σ s).mem := by
  have hsp := hpre.stk
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

/-- The kernel sees the entry's memory but for the frames. -/
theorem kE_bytes {a : Addr} {len : Nat} (hd : (belowA σ.sp entryStack).Disjoint ⟨a, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt (kE p prepared σ s).mem a len = bytesAt σ.mem a len :=
  VG.Proof.MlKem.bytesAt_frame (kE_mem hpre hm) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR; exact (hd.symm.sub_right (sub_frames hpre.stk))) hl

theorem kE_pub : pkOf p (kE p prepared σ s) = pkOf p σ ∧ muOf (kE p prepared σ s) = muOf σ ∧
    sgOf p (kE p prepared σ s) = sgOf p σ := by
  have e0 := kE_gpr hm (r := .r0) (by decide) (by decide) (by decide)
  have e1 := kE_gpr hm (r := .r1) (by decide) (by decide) (by decide)
  have e2 := kE_gpr hm (r := .r2) (by decide) (by decide) (by decide)
  have keySub : Region.Sub (regA (σ.gpr .r0) p.pkLen) (regA (σ.gpr .r0) (publicKeyLen p prepared)) :=
    Region.sub_prefix (by rw [publicKeyLen_eq]; omega)
  have hl := hpre.f_p
  refine ⟨?_, ?_, ?_⟩
  · show bytesAt _ (State.addr ((kE p prepared σ s).gpr .r0)) p.pkLen = _
    rw [e0]; exact kE_bytes hpre hm (hpre.b_p.sub_right keySub) (by rw [publicKeyLen_eq] at hl; omega)
  · show bytesAt _ (State.addr ((kE p prepared σ s).gpr .r1)) 64 = _
    rw [e1]; exact kE_bytes hpre hm hpre.b_m (by decide)
  · show bytesAt _ (State.addr ((kE p prepared σ s).gpr .r2)) p.sigLen = _
    rw [e2]; exact kE_bytes hpre hm hpre.b_s (by have := hpre.f_s; omega)

/-- The kernel's precondition, on entry to it. -/
theorem kE_pre (hc : 0 < p.k) : VPre p kernStack (kE p prepared σ s) := by
  have e0 := kE_gpr hm (r := .r0) (by decide) (by decide) (by decide)
  have e1 := kE_gpr hm (r := .r1) (by decide) (by decide) (by decide)
  have e2 := kE_gpr hm (r := .r2) (by decide) (by decide) (by decide)
  have e3 := kE_gpr hm (r := .r3) (by decide) (by decide) (by decide)
  have ea0 := kE_arg0 hpre hm
  have eaa := kE_argAddr hpre hm
  have esp := kE_sp hm
  have hσ : entryStack ≤ σ.sp.toNat := hpre.stk
  have keySub : Region.Sub (regA (σ.gpr .r0) p.pkLen) (regA (σ.gpr .r0) (publicKeyLen p prepared)) :=
    Region.sub_prefix (by rw [publicKeyLen_eq]; omega)
  have kS : Region.Sub (below (kE p prepared σ s) kernStack) (below σ entryStack) := by
    simp only [below]; rw [esp]; exact sub_kern hσ
  have aS : Region.Sub ⟨(belowA (σ.sp - BitVec.ofNat 32 8) 8).base, 4⟩ (below σ entryStack) :=
    fun x hx => sub_args hσ x (Region.sub_prefix (by decide) x hx)
  have espN : (σ.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8).toNat = σ.sp.toNat - 16 := by
    have : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hσ; omega
    rw [FrameStack.sub_toNat' (by rw [FrameStack.sub_toNat' (by omega)]; omega), FrameStack.sub_toNat' (by omega)]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [vPk, vMu, vSg, vScr, e0, e1, e2, e3, esp]
  · rw [espN]; simp only [entryStack, kernStack] at hσ ⊢; omega
  · rw [State.withRegions_rd]
    simp only [kRd, cacheRdV, cacheRV, eaa, ea0]
  · rw [State.withRegions_wr]; exact hpre.wr
  · exact hpre.d_pc.sub_left keySub
  · exact hpre.d_mc
  · exact hpre.d_sc
  · exact (hpre.b_p.sub_left kS).sub_right keySub
  · exact hpre.b_m.sub_left kS
  · exact hpre.b_s.sub_left kS
  · exact hpre.b_c.sub_left kS
  · have := hpre.f_p; rw [publicKeyLen_eq] at this; omega
  · exact hpre.f_m
  · exact hpre.f_s
  · exact hpre.f_c
  · rw [espN]; have := σ.sp.isLt; omega
  · rw [eaa]; exact hpre.b_c.sub_left aS
  · intro hne
    rw [ea0] at hne ⊢
    cases prepared
    · exact absurd rfl hne
    have hl := hpre.f_p
    have hk : publicKeyLen p true = p.pkLen + 1024 * p.k := by rw [publicKeyLen_eq]; rfl
    rw [hk] at hl
    have ec : State.addr (σ.gpr .r0 + BitVec.ofNat 32 p.pkLen) =
        State.addr (σ.gpr .r0) + BitVec.ofNat 64 p.pkLen := addr_add (by omega)
    have cS : Region.Sub ⟨State.addr (σ.gpr .r0 + BitVec.ofNat 32 p.pkLen), 1024 * p.k⟩
        (regA (σ.gpr .r0) (publicKeyLen p true)) := by rw [ec]; exact Offset.sub_base _ (by rw [hk])
    simp only [cacheRV, ea0, cacheV, ite_true]
    refine ⟨hpre.d_pc.sub_left cS, (hpre.b_p.sub_left kS).sub_right cS, ?_, fun i hi => ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.pkLen) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · have hb : bytesAt (kE p true σ s).mem (State.addr (σ.gpr .r0)) (preparedPublicKeyBytes p) =
          bytesAt σ.mem (State.addr (σ.gpr .r0)) (preparedPublicKeyBytes p) :=
        kE_bytes hpre hm hpre.b_p (by have : publicKeyLen p true = preparedPublicKeyBytes p := rfl; omega)
      have hP := PreparedKey.preparedPublicKey_of_bytes hb (hpre.key rfl)
      have := (preparedPublicKey_iff.mp hP) i hi
      rw [ec, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact this

/-- The regions the kernel is given are the entry's, and its argument. -/
theorem kE_covers (hc : 0 < p.k) : Covers (kRd p prepared σ ++ σ.wr) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) ∧
    Covers σ.wr (pushed [.r12, .lr] s).wr := by
  have hrd := hpre.rd
  have n1 := hpre.f_p
  have h8 : 8 ≤ (σ.sp - BitVec.ofNat 32 8).toNat := by
    rw [← hm.sp]; exact kE_sp8 hpre hm
  refine ⟨VG.Proof.MlDsa.Arm.Message.covers_of_within fun r hr => ?_,
    fun a n ⟨R, hR, hc⟩ => ⟨R, by rw [pushed_wr, hm.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR), hc⟩⟩
  simp only [pushed_rd, pushed_wr, hm.rd, hm.wr, hm.sp, hrd]
  simp only [kRd, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with rfl | rfl | rfl | rfl | hr | hr
  · exact ⟨regA (σ.gpr .r0) (publicKeyLen p prepared), by simp, within_base _ (by rw [publicKeyLen_eq]; omega)⟩
  · exact ⟨_, by simp, within_self _⟩
  · exact ⟨_, by simp, within_self _⟩
  · refine ⟨⟨State.addr (σ.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8), 8⟩, by simp, ?_⟩
    show Within ⟨State.addr (σ.sp - BitVec.ofNat 32 8) - BitVec.ofNat 64 8, 4⟩ _
    rw [FrameStack.addr_sub' h8]; exact within_base _ (by decide)
  · cases prepared
    · simp [cacheV] at hr
    · have hk : publicKeyLen p true = p.pkLen + 1024 * p.k := by rw [publicKeyLen_eq]; rfl
      simp only [cacheV, ite_true, List.mem_ite_nil_left, List.mem_singleton] at hr
      rcases hr with h | ⟨-, hr⟩
      · simp at h
      refine ⟨regA (σ.gpr .r0) (publicKeyLen p true), by simp, ?_⟩
      rw [hk] at n1
      have ec : State.addr (σ.gpr .r0 + BitVec.ofNat 32 p.pkLen) =
          State.addr (σ.gpr .r0) + BitVec.ofNat 64 p.pkLen := addr_add (by omega)
      rw [hr, ec]; exact within_off _ (by rw [hk])
  · exact ⟨r, by simp [hr], within_self _⟩

end

/-! ## The entries -/

/-- One of the parameter sets of Table 1. -/
abbrev Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

theorem withCache_stack {p : Params} (h3 : Ok3 p) : FrameStack.armStack (withCache prims p) ≤ kernStack := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

/-- The word `r4` was pushed to, by the entry's frame, is kept by the call. -/
theorem r4_kept {p : Params} {prepared : Bool} {σ s s₃ : State} (hpre : VE p prepared entryStack σ)
    (hm : Mid p prepared σ s) (hf : Frame (σ.wr ++ [Argon2.Arm.stkR s.sp 44]) s.mem s₃.mem) :
    s₃.mem.readW (State.addr (σ.sp - BitVec.ofNat 32 8)) 32 = σ.gpr .r4 := by
  have hsp := hpre.stk
  have h16 : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hsp; omega
  have h8 : 8 ≤ σ.sp.toNat := by omega
  have hsub : Region.Sub ⟨State.addr (σ.sp - BitVec.ofNat 32 8), 4⟩ (below σ entryStack) := by
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
    · rw [hpre.wr, List.mem_singleton] at hr
      subst hr
      exact hpre.b_c.sub_left hsub
    · rw [List.mem_singleton] at hr; subst hr
      rw [hm.sp]
      show Region.Disjoint ⟨State.addr (σ.sp - BitVec.ofNat 32 8), 4⟩
        ⟨State.addr (σ.sp - BitVec.ofNat 32 8) - BitVec.ofNat 64 44, 44⟩
      exact Offset.base_disjoint_below (State.addr (σ.sp - BitVec.ofNat 32 8)) (n := 44) (k := 4) (by omega)

theorem entry_correct {p : Params} (h3 : Ok3 p) (prepared : Bool) (σ : State)
    (hpre : (verifyE p prepared entryStack).pre σ) :
    ∃ t s', Exec isa (verifyEntry prims p prepared) σ t s' ∧ abiPreserved σ s' ∧
      (verifyE p prepared entryStack).post σ s' := by
  have hpre' : VE p prepared entryStack σ := hpre
  have hσ := hpre'.stk
  have h16 : 16 ≤ σ.sp.toNat := by simp only [entryStack] at hσ; omega
  have hF := vfacts h3
  have hc : 0 < p.k := by have := hF.k; omega
  unfold verifyEntry
  refine (WP.frame (rs := [.r4, .lr]) (r := .r4) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega) (by decide) ?_).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  refine WP.seq (WP.mono (blockA_ok p prepared σ) fun s₁ hm => ?_)
  have cov := kE_covers hpre' hm hc
  refine WP.seq (Argon2.Arm.frameCall_ok (rs := [.r12, .lr]) (t := .r12) (by decide) (by decide) (by decide)
    (withCache_correct prims_ok hF (STK := kernStack) (by decide)) (K := 44) (by
      have := withCache_stack h3; simp only [List.length_cons, List.length_nil, kernStack] at this ⊢; omega)
    (by rw [hm.sp, FrameStack.sub_toNat' (by omega)]; simp only [entryStack] at hσ; omega)
    (kE_pre hpre' hm hc) cov.1 cov.2 fun s₂ hA hpost => ?_)
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun σ₄ u₄ => WP.block_nil ?_
  have r4' : σ₄.gpr .lr = σ.gpr .lr := by rw [u₄.gpr, hA.cs .r4 (by decide) (by decide), hm.r4]
  have sp4 : σ₄.sp = σ.sp - BitVec.ofNat 32 8 := by rw [u₄.sp, hA.sp, hm.sp]
  have hw4 : σ₄.mem.readW (State.addr σ₄.sp) 32 = σ.gpr .r4 := by
    rw [sp4, u₄.mem]; exact r4_kept hpre' hm hA.frame
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4
      show (σ₄.setReg .r4 (σ₄.mem.readW (State.addr σ₄.sp) 32)).gpr .r4 = _
      rw [RegUpd.gpr_setReg_self]; exact hw4
    · rw [popped_gpr h4]
      by_cases hl : r = .lr
      · subst hl; exact r4'
      · have h12 : r ≠ .r12 := by rintro rfl; revert hr; decide
        rw [u₄.other r hl, hA.cs r hr hl, hm.gpr r h4 h12]
  · rw [popped_sp, sp4]; exact BitVec.sub_add_cancel _ _
  · obtain ⟨b0, b1, b2⟩ := kE_pub hpre' hm
    have hpost' : VOut p (kE p prepared σ s₁) ((s₂.withRegions (kRd p prepared σ) σ.wr).gpr .r0) := hpost
    have g0 : (popped .r4 (4 * [Reg.r4, .lr].length) σ₄).gpr .r0 = s₂.gpr .r0 := by
      rw [popped_gpr (by decide), u₄.other _ (by decide), popped_gpr (by decide)]
    show VOut p σ _
    rw [g0]
    rw [State.withRegions_gpr] at hpost'
    unfold VOut vv at hpost' ⊢
    rw [b0, b1, b2] at hpost'
    exact hpost'

/-! ## Constant time -/

theorem setC_nomem (p : Params) (prepared : Bool) :
    ∀ i ∈ (([.mov .r4 (.reg .lr)] : List Instr) ++ setCache p prepared), ∀ s, isa.addrs i s = [] := by
  intro i hi s
  cases prepared <;>
    simp only [setCache, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem entry_ct {p : Params} (h3 : Ok3 p) (prepared : Bool) :
    ConstantTime isa (verifyE p prepared entryStack).pre (verifyE p prepared entryStack).pub
      (verifyEntry prims p prepared) := by
  have hF := vfacts h3
  have hc : 0 < p.k := by have := hF.k; omega
  unfold verifyEntry
  refine RelCT.constantTime (RelCT.frame (fun s₁ s₂ h => h.2.2.1) ?_)
  refine RelCT.mono (P := fun a b => ∃ q : State × State, ((verifyE p prepared entryStack).pre q.1 ∧
      (verifyE p prepared entryStack).pre q.2 ∧ (verifyE p prepared entryStack).pub q.1 q.2) ∧
      a = pushed [.r4, .lr] q.1 ∧ b = pushed [.r4, .lr] q.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨σ₁, σ₂⟩ => ?_
  refine RelCT.seq (RelCT.wp (F₁ := fun s => ((verifyE p prepared entryStack).pre σ₁ ∧
      (verifyE p prepared entryStack).pre σ₂ ∧ (verifyE p prepared entryStack).pub σ₁ σ₂) ∧ Mid p prepared σ₁ s)
    (F₂ := Mid p prepared σ₂) (block_nomem_tr (setC_nomem p prepared))
    fun a b ⟨h, ha, hb⟩ => ⟨ha ▸ WP.mono (blockA_ok p prepared σ₁) fun _ e => ⟨h, e⟩,
      hb ▸ blockA_ok p prepared σ₂⟩) ?_
  refine RelCT.seq (Argon2.Arm.frameCall_rel (rs := [.r12, .lr]) (t := .r12) (by decide)
    (withCache_correct prims_ok hF (STK := kernStack) (by decide)) (withCache_ct prims_ok hF (by decide))
    (kRd p prepared σ₁) σ₁.wr fun x y ⟨_, ⟨⟨h₁, h₂, hp⟩, m₁⟩, m₂⟩ => ?_)
    (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
  have hp0 := hp
  obtain ⟨psp, p0, p1, p2, p3, -, -, -⟩ := hp0
  have h₁' : VE p prepared entryStack σ₁ := h₁
  have h₂' : VE p prepared entryStack σ₂ := h₂
  have erd : kRd p prepared σ₂ = kRd p prepared σ₁ := by simp only [kRd, p0, p1, p2, psp]
  have ewr : σ₂.wr = σ₁.wr := by rw [h₁'.wr, h₂'.wr, p3]
  have hEq : (pushed [.r12, .lr] y).callEntry.withRegions (kRd p prepared σ₁) σ₁.wr = kE p prepared σ₂ y := by
    simp only [kE, erd, ewr]
  have cov₂ := kE_covers h₂' m₂ hc
  rw [erd, ewr] at cov₂
  rw [hEq]
  refine ⟨by rw [m₁.sp, m₂.sp, psp], kE_pre h₁' m₁ hc, kE_pre h₂' m₂ hc, ?_, (kE_covers h₁' m₁ hc).1,
    (kE_covers h₁' m₁ hc).2, cov₂.1, cov₂.2⟩
  have g₁ : ∀ r, r ∉ linkRegs → r ≠ .r4 → r ≠ .r12 → (kE p prepared σ₁ x).gpr r = σ₁.gpr r :=
    fun r a b c => kE_gpr m₁ a b c
  have g₂ : ∀ r, r ∉ linkRegs → r ≠ .r4 → r ≠ .r12 → (kE p prepared σ₂ y).gpr r = σ₂.gpr r :=
    fun r a b c => kE_gpr m₂ a b c
  obtain ⟨b₁0, b₁1, b₁2⟩ := kE_pub h₁' m₁
  obtain ⟨b₂0, b₂1, b₂2⟩ := kE_pub h₂' m₂
  have hp' := hp
  obtain ⟨-, -, -, -, -, pk, mu, sg⟩ := hp'
  refine ⟨by rw [kE_sp m₁, kE_sp m₂, psp], ?_, ?_, ?_, ?_, by rw [b₁0, b₂0, pk], by rw [b₁1, b₂1, mu],
    by rw [b₁2, b₂2, sg], by rw [kE_arg0 h₁' m₁, kE_arg0 h₂' m₂, p0]⟩
  all_goals simp only [vPk, vMu, vSg, vScr]
  all_goals rw [g₁ _ (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)]
  exacts [p0, p1, p2, p3]

end VG.Proof.MlDsa.Arm.Verify
