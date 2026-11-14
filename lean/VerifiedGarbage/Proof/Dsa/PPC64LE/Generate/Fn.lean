module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.DeriveCall
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Check
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Ctx
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.Dsa.RandomResult
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Range
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Spec
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Sampler
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
public import VerifiedGarbage.Spec.Dsa.Derive

/-! ### `Dsa.PPC64LE.Generate.Finish`, which only this module used -/

section

/-!
# DSA key generation on PPC64LE: the exit

`finish_ok`: unless the status is 1, `out` is zeroed; the nonce is zeroed,
the octets consumed are written to `used`, the status returned and the
registers restored (`Fin`); after the frame is freed, that meets the
contract (`fin_post`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

theorem ctx_r3 : ∀ r ∈ ctxRegs, r ∉ ([.r3] : List Reg) := by decide

theorem ctx_31 : ∀ r ∈ ctxRegs, r ∉ ([.r31] : List Reg) := by decide

theorem ctx_012 : ∀ r ∈ ctxRegs, r ∉ ([.r0, .r12] : List Reg) := by decide

theorem ctx_z : ∀ r ∈ ctxRegs, r ∉ (([.r0, .r16, .r17] : List Reg) ++ ([.r16, .r17] : List Reg)) := by decide

theorem preserved_nv : ∀ r ∈ preserved, r = .r2 ∨ ∃ i < 18, r = nv i := by decide

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : GL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside L.F (oNonce + o) n m m') : Frame [L.outR, L.scrR, L.nR] m m' := by
  intro x hx
  have hF := hL.fnw
  refine ho x ?_
  have hn := hx L.nR (by simp)
  simp only [Region.Contains, off] at hn
  rw [VG.Offset.toNat_sub_add x L.F (by simp only [oNonce]; omega_using [])] at hn
  simp only [ofs, oNonce, frameBytes] at hn hF ⊢
  have := (x - L.F).isLt
  by_contra hc
  rw [show 2 ^ 64 - 120 + (x - L.F).toNat = (x - L.F).toNat - 120 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])] at hn
  omega

/-- The length of the key, into `r17`. -/
abbrev olen : List Instr := [.add .r17 .r20 .r20, .add .r17 .r17 .r20, .add .r17 .r17 .r21, .add .r17 .r17 .r21]

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  r3 : t.gpr .r3 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol = R.key.getD (List.replicate (glOf s₀).ol 0)
  used : t.mem.readW (glOf s₀).used 64 = BitVec.ofNat 64 R.used
  nv : ∀ i < 18, t.gpr (nv i) = s₀.gpr (nv i)
  r2 : t.gpr .r2 = s₀.gpr .r2
  lr : t.lr = s₀.lr
  sp : t.sp = (glOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.GenerateKeyResult} (h : gkContract.pre s₀)
    (hc : Ctx (glOf s₀) s₀ t) (h25 : t.gpr .r25 = BitVec.ofNat 64 R.used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
      R.key.getD (List.replicate (glOf s₀).ol 0))
    (hnone : R.status ≠ 1 → R.key = none) :
    WP isa (finish olen) t (Fin s₀ R) := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (WP.keep (c := .block [.subi .r3 .r31 1]) [.r3] (Q := fun t₁ => t₁.mem = t.mem ∧
    t₁.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₁ ⟨⟨m1, a3⟩, k1⟩ => ?_)
  have hc₁ : Ctx (glOf s₀) s₀ t₁ := hc.step hL k1.sp k1.rd k1.wr (fun r hr => k1.gpr r (ctx_r3 r hr))
    (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (glOf s₀) s₀ t₂ → Keep [.r0, .r3, .r16, .r17] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (glOf s₀).out (glOf s₀).ol =
        R.key.getD (List.replicate (glOf s₀).ol 0) → P t₂) →
      WP isa (.ite (.zero .d .r3) (.block []) (zeroOut olen)) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [eval_zero, a3, h31, RS.sub1_beq _ (by omega_using [hst])]) (fun hs => ?_)
      (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      refine WP.seq (WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t₂ => t₂.gpr .r0 = 0 ∧
        t₂.gpr .r16 = off (glOf s₀).out 0 ∧ t₂.gpr .r17 = BitVec.ofNat 64 (glOf s₀).ol ∧ t₂.mem = t₁.mem)
        (by prun [hc₁.r18, hc₁.r20, hc₁.r21, ← BitVec.ofNat_add]; exact ⟨rfl, by simp only [GL.ol]; congr 1; omega_using []⟩)
        (by decide))
        fun t₂ ⟨⟨b0, b16, b17, m2⟩, k2⟩ => ?_)
      have ho : Scr t₂ (glOf s₀).out (glOf s₀).ol :=
        Scr.of_mem (by rw [k2.wr, hc₁.wr, hwr]; simp) hL.nwOut
      refine WP.mono (zeroLoop_ok (by simp only [GL.ol]; omega_using [hq]) (by simp only [GL.ol]; omega_using [hq, hp]) ho b0 b16 b17)
        fun t₃ ⟨⟨z3, o3⟩, k3⟩ => ?_
      refine hP t₃ (hc₁.step hL (k2.trans k3).sp (k2.trans k3).rd (k2.trans k3).wr
        (fun r hr => (k2.trans k3).gpr r (ctx_z r hr)) ?_) ((k2.trans k3).mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega_using [hc'])
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c25 : t₂.gpr .r25 = BitVec.ofNat 64 R.used := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h25)
  have c31 : t₂.gpr .r31 = BitVec.ofNat 64 R.status := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h31)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)) fun t₃ ⟨⟨_, _, o3⟩, k3⟩ => ?_
  have hc₃ : Ctx (glOf s₀) s₀ t₃ := hc₂.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_012 r hr))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr ((glOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [hc₃.wr, hwr, BitVec.add_zero]
    exact ⟨(glOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hus' : InRegions t₃.wr (glOf s₀).used 8 := by rw [← BitVec.add_zero (glOf s₀).used]; exact hus
  refine WP.mono (WP.keep (c := .block [.store .d .r25 .r30 0, .addi .r3 .r31 0]) [.r3] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW ((glOf s₀).used + BitVec.ofNat 64 0) (BitVec.ofNat 64 R.used) ∧
      t₄.gpr .r3 = BitVec.ofNat 64 R.status)
    (by prun [hc₃.r30, (k3.gpr _ (by decide)).trans c25, (k3.gpr _ (by decide)).trans c31, hus, hus', add0]) (by decide))
    fun t₄ ⟨⟨m4, a3⟩, k4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (glOf s₀).usedR.Contains ((glOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (glOf s₀).F d) 64 = t₃.mem.readW (off (glOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (GL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hin : ∀ i < 19, InRegions (t₄.rd ++ t₄.wr) (off (glOf s₀).F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k4.rd, k4.wr, hc₃.rd, hc₃.wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains hL rfl (by simp only [oSave]; omega_using [])
      (by simp only [oSave, frameBytes]; omega_using [hi])⟩
  refine WP.mono (restoreRegs_ok t₄ (k4.sp.trans hc₃.sp) hin
    (fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi])).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.lr)) fun t₅ ⟨r5, l5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, r5, ?_, l5, sp5.trans (k4.sp.trans hc₃.sp), rd5.trans (k4.rd.trans hc₃.rd),
    wr5.trans (k4.wr.trans hc₃.wr)⟩
  · rw [o5 .r3 (by decide) (by decide) (by decide)]; exact a3
  · rw [m5, m4, RS.bytes_frame (rs := [(glOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by simp only [GL.ol]; omega_using [hq, hp])]
    rw [bytes_outside (o3.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using [])) hL.dFO
      (by simp only [GL.ol]; omega_using [hq, hp])]
    exact o2
  · rw [m5, m4, BitVec.add_zero, Mem.readW_writeW_self64]
  · rw [o5 .r2 (by decide) (by decide) (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact hc₂.r2

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : gkContract.pre s₀) (hst : (gkRes s₀).status ≤ 2) (hf : Fin s₀ (gkRes s₀) t) :
    abiPreserved s₀ (freed frameBytes t) ∧ gkContract.post s₀ (freed frameBytes t) := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.lr⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    rcases preserved_nv r hr with rfl | ⟨i, hi, rfl⟩
    · exact hf.r2
    · exact hf.nv i hi
  · simp only [freed, hf.sp, GL.F, glOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.r3, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  · simp only [freed]
    have e3 : s₀.gpr .r3 = (glOf s₀).out := rfl
    have e4 : (s₀.gpr .r4).toNat = (glOf s₀).ol := hol
    rw [e3, e4]; exact hf.out
  · simp only [freed, Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) hf.used

end VG.Proof.Dsa.PPC64LE.GK

end

end


/-!
# DSA key generation on PPC64LE: the function

`generate_correct`: `vg_dsa_generate_key` meets `gkContract`. In its frame,
the entry (`entry_ok`), the check of the domain (`checked_ok`), then for a
valid domain the scan of q (`prepareQ_ok`), the sampling (`sample_ok`) and
the derivation (`derive_ok`, by `vg_dsa_derive_key_checked`, for the
checked domain), and the exit (`finish_ok`) follow one
another; the result is `generateKeyBytes`'s (`gkRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa.Random (sampleStatus)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)

/-- The draw of x. -/
abbrev drawOf (s₀ : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (qOf s₀) 128 (randOf (glOf s₀) s₀.mem)

/-- The domain, on entry. -/
abbrev parOf (s₀ : State) : List Byte := Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl

/-- The key derived from `x`. -/
abbrev dkOf (s₀ : State) (x : Nat) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (Spec.Dsa.encodeBE (glOf s₀).ql x)

/-- The result, by the domain's check and the draw. -/
abbrev resOf (s₀ : State) : Spec.Dsa.GenerateKeyResult :=
  if chkOf s₀ then
    match (drawOf s₀).scalar with
    | none => ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used, (drawOf s₀).trace⟩
    | some x => ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩
  else ⟨none, 0, 0, [4]⟩

theorem gkRes_eq {s₀ : State} (h : gkContract.pre s₀) : gkRes s₀ = resOf s₀ := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hkl, -⟩ := h
  have e7 : (s₀.gpr .r7).toNat = (glOf s₀).kl := hkl
  have hq' : (Spec.Dsa.paramsBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀)).q = qOf s₀ := by
    rw [VG.Proof.Dsa.paramsBytes_eq]
    show Spec.Dsa.decodeBE _ = Spec.Dsa.decodeBE _
    rw [VG.Proof.Dsa.bytesAt_slice s₀.mem _ (by simp only [GL.kl]; omega_using [])]
  unfold gkRes
  rw [e7]
  show Spec.Dsa.generateKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (randOf (glOf s₀) s₀.mem) = _
  rw [VG.Proof.Dsa.generateKeyBytes_eq hL.lv (by rw [VG.Proof.Bignum.bytesAt_length])]
  simp only [hq']
  rfl

theorem resOf_status (s₀ : State) : (resOf s₀).status ≤ 2 := by
  unfold resOf
  split
  · split
    · dsimp only; split <;> omega_using []
    · dsimp only; unfold Spec.Dsa.signStatus; split <;> omega_using []
  · dsimp only; omega_using []

theorem resOf_none {s₀ : State} (hs : (resOf s₀).status ≠ 1) : (resOf s₀).key = none := by
  revert hs
  unfold resOf
  split
  · split
    · intro _; rfl
    · dsimp only
      intro hs
      unfold Spec.Dsa.signStatus at hs
      split at hs
      · exact absurd rfl hs
      · rename_i hn; simpa using hn
  · intro _; rfl

/-- A frame's octet is kept by a call that writes regions apart from the frame. -/
theorem frame_byte {L : GL} (hL : L.Ok) {rs : List Region} (hd : ∀ r ∈ rs, L.frR.Disjoint r) {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hdl : d < frameBytes) : m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  have hin : L.frR.Contains (off L.F d) 1 :=
    VG.Offset.contains_base _ (by omega_using [hdl]) (by simp only [frameBytes] at hdl; omega_using [hdl])
  exact hd r hr _ hin hc

/-- After the check of the domain. -/
structure Chk (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off (glOf s₀).F (oNonce + j)) = 0
  r3 : ((t.gpr .r3).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem checked_ok {s₀ t : State} (h : gkContract.pre s₀) (he : Entered (glOf s₀) s₀ t) :
    WP isa (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters)) t
      (Chk s₀) := by
  have hL := glOf_ok h
  refine WP.seq (WP.mono (checkArgs_ok hL he.ctx) fun t₂ ⟨ca, m2, k2⟩ => WP.mono (check_ok h ca) fun t₃ ck => ?_)
  refine ⟨ck.ctx, (ck.pres _ (by decide)).trans ((k2.gpr _ (by decide)).trans he.r25), fun j hj => ?_, ck.r3⟩
  rw [frame_byte hL (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dFS) ck.frame
    (by simp only [oNonce, frameBytes]; omega_using [hj]), m2]
  exact he.nonce j hj

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (glOf s₀).ql - (eOf s₀).W, m (off (glOf s₀).F (oNonce + j)) = 0

/-- The derivation, from the sampler's result. -/
theorem derive_wp {s₀ t : State} (h : gkContract.pre s₀) (hq : 1 < qOf s₀) (hc : Ctx (glOf s₀) s₀ t)
    (hz : NZero s₀ t.mem) (h25 : t.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 (sampleStatus (drawOf s₀)))
    (hk : ∀ x, (drawOf s₀).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₀) t.mem) = x)
    (hchk : chkOf s₀ = true) :
    WP isa Impl.Dsa.PPC64LE.Generate.derive t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used ∧
        t'.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status ∧
        ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t'.mem (glOf s₀).out (glOf s₀).ol =
          (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) := by
  have hL := glOf_ok h
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hst := sampleStatus_le (drawOf s₀)
  unfold Impl.Dsa.PPC64LE.Generate.derive
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t.mem ∧
    t₂.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_)
  have c₂ : Ctx (glOf s₀) s₀ t₂ :=
    hc.step hL k2.sp k2.rd k2.wr (fun r hr => k2.gpr r (ctx_r3 r hr)) (by rw [m2]; exact Frame.refl _ _)
  have b25 : t₂.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used := (k2.gpr _ (by decide)).trans h25
  refine WP.ite (decide (sampleStatus (drawOf s₀) = 1))
    (by rw [eval_zero, a3, h31, RS.sub1_beq _ (by omega_using [hst])]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (RS.sampleStatus_some.mp hs)
    have hR : resOf s₀ = ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    have hnonce : Spec.Rsa.bytesAt t₂.mem (off (glOf s₀).F oNonce) (glOf s₀).ql =
        Spec.Dsa.encodeBE (glOf s₀).ql x := by
      rw [m2]
      exact RS.nonce_eq (W := (eOf s₀).W) hE.Wq hz (hk x hx)
    refine WP.seq (WP.mono (deriveArgs_ok hL c₂) fun t₃ ⟨da, m3, k3⟩ => ?_)
    refine WP.seq (WP.mono (derive_ok h da hchk) fun t₄ dv => ?_)
    have es : dresOf (glOf s₀) t₃.mem = dkOf s₀ x := by
      simp only [dresOf, dkOf, parOf]; rw [m3, c₂.par, hnonce]
    have hr3 := dv.r3
    rw [es] at hr3
    unfold deriveFinish
    refine WP.ite (decide (Spec.Dsa.signStatus (dkOf s₀ x) = 0))
      (by rw [RS.eval_zero_w, RS.setWidth_beq_zero hr3]) (fun hz' => ?_) (fun hz' => ?_)
    · simp only [decide_eq_true_eq] at hz'
      refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₅ => t₅.mem = t₄.mem ∧
        t₅.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₅ ⟨⟨m5, a31⟩, k5⟩ => ?_
      refine ⟨dv.ctx.step hL k5.sp k5.rd k5.wr (fun r hr => k5.gpr r (ctx_31 r hr))
        (by rw [m5]; exact Frame.refl _ _), ?_, ?_, fun _ => ?_⟩
      · rw [k5.gpr _ (by decide), dv.pres _ (by decide), k3.gpr _ (by decide), b25, hR]
      · rw [a31, hR]; dsimp only; rw [hz']
      · rw [m5, dv.out, es, hR]
    · simp only [decide_eq_false_iff_not] at hz'
      refine WP.mono (WP.keep (c := .block [.li .r31 1]) [.r31] (Q := fun t₅ => t₅.mem = t₄.mem ∧
        t₅.gpr .r31 = BitVec.ofNat 64 1) (by prun) (by decide)) fun t₅ ⟨⟨m5, a31⟩, k5⟩ => ?_
      refine ⟨dv.ctx.step hL k5.sp k5.rd k5.wr (fun r hr => k5.gpr r (ctx_31 r hr))
        (by rw [m5]; exact Frame.refl _ _), ?_, ?_, fun _ => ?_⟩
      · rw [k5.gpr _ (by decide), dv.pres _ (by decide), k3.gpr _ (by decide), b25, hR]
      · rw [a31, hR]; dsimp only
        unfold Spec.Dsa.signStatus at hz' ⊢
        split at hz' <;> simp_all
      · rw [m5, dv.out, es, hR]
  · simp only [decide_eq_false_iff_not] at hs
    have hx : (drawOf s₀).scalar = none := by
      cases hc' : (drawOf s₀).scalar with
      | none => rfl
      | some k => exact absurd (RS.sampleStatus_some.mpr (by rw [hc']; rfl)) hs
    have hR : resOf s₀ = ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used,
        (drawOf s₀).trace⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    refine WP.block_nil ⟨c₂, by rw [b25, hR], ?_, fun h1 => ?_⟩
    · rw [(k2.gpr _ (by decide)).trans h31, hR]
      simp only [sampleStatus, hx]
    · rw [hR] at h1 ⊢
      exact absurd h1 (by dsimp only; split <;> decide)

theorem ctx_draw : ∀ r ∈ ctxRegs, r ∉ drawRegs := by decide

/-- After the steps for a valid domain. -/
structure VOut (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used
  r31 : t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)

theorem valid_ok {s₀ t₂ : State} (h : gkContract.pre s₀) (ck : Chk s₀ t₂) (hchk : chkOf s₀ = true) :
    WP isa valid t₂ (VOut s₀) := by
  have hL := glOf_ok h
  have hql := hL.ql
  unfold valid
  refine WP.seq (WP.mono (prepareQ_ok h ck.ctx) fun t₃ ⟨sc, h0, m3, k3⟩ => ?_)
  have c25 : t₃.gpr .r25 = BitVec.ofNat 64 0 := (k3.gpr _ (by decide)).trans ck.r25
  refine WP.ite (decide (¬ 1 < qOf s₀)) (by rw [eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_)
  · -- q ≤ 1: no draw.
    simp only [decide_eq_true_eq] at hq
    have hd : drawOf s₀ = ⟨none, 0, [4]⟩ := by
      show Spec.Dsa.Random.sample (qOf s₀) (127 + 1) _ = _
      rw [Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega_using [hq])]
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk, hd]; rfl
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₄ => t₄.mem = t₃.mem ∧
      t₄.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₄ ⟨⟨m4, a31⟩, k4⟩ => ?_
    refine ⟨sc.ctx.step hL k4.sp k4.rd k4.wr (fun r hr => k4.gpr r (ctx_31 r hr))
      (by rw [m4]; exact Frame.refl _ _), ?_, ?_, fun h1 => ?_⟩
    · rw [k4.gpr _ (by decide), c25, hR]
    · rw [a31, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- q > 1: the draw and the derivation.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have hQ := seOf_Q (L := glOf s₀) s₀.mem hq
    have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
    have hql' : (eOf s₀).ql ≤ 32 := hE.ql
    have hF := hL.fnw
    refine WP.seq (WP.mono (sample_ok hE hQ (sc.env h hq) c25 (Nat.zero_le _)) fun t₄ so => ?_)
    rw [List.drop_zero] at so
    have c₄ : Ctx (glOf s₀) s₀ t₄ := sc.ctx.step hL so.keep.sp so.keep.rd so.keep.wr
      (fun r hr => so.keep.gpr r (ctx_draw r hr))
      (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega_using [hW, hql']) so.out)
    have nz : NZero s₀ t₄.mem := fun j hj => by
      have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
        Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega_using [hql, hj])
      have hj' : oNonce + j < (eOf s₀).o := by
        have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
        simp only [SE.o]; omega_using [hj, e2]
      rw [so.out _ (.inl (by rw [e]; exact hj')), m3]
      exact ck.nonce j (by omega_using [hql, hj])
    have r25 : t₄.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used := by rw [so.r25, Nat.zero_add]
    exact WP.mono (derive_wp h hq c₄ nz r25 so.r31 so.cand hchk) fun t₅ ⟨c, a, b, d⟩ => ⟨c, a, b, d⟩


theorem generate_correct (s₀ : State) (h : gkContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.PPC64LE.Generate.code s₀ tr t ∧ abiPreserved s₀ t ∧ gkContract.post s₀ t := by
  show WP isa Impl.Dsa.PPC64LE.Generate.code s₀ fun t => abiPreserved s₀ t ∧ gkContract.post s₀ t
  have hL := glOf_ok h
  have hql := hL.ql
  have hfin : ∀ t, Ctx (glOf s₀) s₀ t → t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
        (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) →
      WP isa (finish olen) t fun t' =>
        abiPreserved s₀ (freed frameBytes t') ∧ gkContract.post s₀ (freed frameBytes t') :=
    fun t hc h25 h31 hsig => WP.mono (finish_ok h hc h25 h31 (resOf_status s₀) hsig resOf_none) fun t' hf =>
      fin_post h (by rw [gkRes_eq h]; exact resOf_status s₀) (by rw [gkRes_eq h]; exact hf)
  unfold Impl.Dsa.PPC64LE.Generate.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.PPC64LE.Generate.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (checked_ok h he) fun t₂ ck => ?_)
  refine WP.seq (WP.ite (decide ((if chkOf s₀ then 1 else 0) = 0))
    (by rw [RS.eval_zero_w, RS.setWidth_beq_zero ck.r3]) (fun hc => ?_) (fun hc => ?_))
  · -- An invalid domain.
    have hchk : chkOf s₀ = false := by
      cases hc' : chkOf s₀ <;> simp_all
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk]; rfl
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₃ ⟨⟨m3, a31⟩, k3⟩ => ?_
    refine hfin t₃ (ck.ctx.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_31 r hr))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => ?_
    · rw [k3.gpr _ (by decide), ck.r25, hR]
    · rw [a31, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- A valid domain.
    have hchk : chkOf s₀ = true := by
      cases hc' : chkOf s₀ <;> simp_all
    exact WP.mono (valid_ok h ck hchk) fun t₄ v => hfin t₄ v.ctx v.r25 v.r31 v.out

end VG.Proof.Dsa.PPC64LE.GK
