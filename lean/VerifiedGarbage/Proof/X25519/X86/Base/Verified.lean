import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.X25519.X86.Base
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Base.Lit`. -/
section

/-! `vg_x25519_base`'s code as literals (`materialize_code`), for the
constant-time checks and `spSafe`. -/
namespace VG.Impl.X25519.X86.Base
open VG VG.X86 VG.Impl.Ed25519.X86

materialize_code x25519BaseStartBlock := (.block x25519BaseStart : Prog isa)
materialize_code x25519BaseFinishTail :=
  (.block (outputWords 64 8 ++ Impl.X25519.X86.restore) : Prog isa)
materialize_code x25519Base

end VG.Impl.X25519.X86.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Base.Main`. -/
section

/-!
# X25519 of the base point on x86: correctness

The scalar's bits are expanded and clamped (`clampBits_ok`: the bits of
`decodeScalar25519 k`), the comb computes a representative of `[k] B`
(`combMultiply_ok`), and `uEncode` its u-coordinate `(Z + Y) / (Z - Y)`,
which is `X25519(k, 9)` (`Proof/X25519/Edwards/Ladder.lean`).
-/

namespace VG.Proof.X25519.X86.Base

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86.Base
open VG.Proof.Ed25519.X86
open VG.Proof.Ed25519 (Rep baseAff)

/-- The contract the proof is written against: `vg_ed25519_scalar_base`'s
precondition (the same arguments), with `X25519(k, 9)` as postcondition. -/
def x25519BaseLocal : Contract isa :=
  { scalarBaseLocal with
    post := fun s t => Spec.X25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
      Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
        Spec.X25519.basePoint }

/-! ## Clamping -/

/-- The bits of the decoded scalar: those of the bytes read as a number
(`Spec.Ed25519.decodeLE`), but for the clamped ones: bits 0–2 and 255 are 0,
bit 254 is 1. -/
theorem clamp_bit {kb : List Byte} (hl : kb.length = 32) {k : Nat} (hk : k < 256) :
    Spec.X25519.decodeScalar25519 kb / 2 ^ k % 2 =
      if k = 254 then 1 else if k = 255 then 0 else if k = 2 then 0 else if k = 1 then 0 else
      if k = 0 then 0 else Spec.Ed25519.decodeLE kb / 2 ^ k % 2 := by
  by_cases h255 : k = 255
  · subst h255
    have := Proof.X25519.Edwards.decodeScalar25519_shift hl
    rw [Nat.shiftRight_eq_div_pow] at this
    rw [this]; rfl
  · have e := VG.Proof.X25519.scalar_bit hl (t := k) (by omega)
    simp only [Proof.X25519.bit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at e
    rw [e, VG.Proof.Ed25519.decodeLE_eq]
    have hb := VG.Proof.X25519.leNum_bit kb k
    simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb
    rw [hb]
    by_cases h3 : k < 3
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
    · by_cases h254 : k = 254
      · subst h254; rfl
      · have h2 : k ≠ 2 := by omega
        have h1 : k ≠ 1 := by omega
        have h0 : k ≠ 0 := by omega
        simp only [h3, h254, h255, h2, h1, h0, ite_false]


theorem storeBit_ok {x : BitVec 32} {s : State} (hc : Ed25519.X86.Ctx x s) {q v : Nat} (hq : q < 256)
    (hv : v < 2) :
    WP isa (.block (storeBit q v)) s fun t => VG.Proof.X25519.X86.Keep s t ∧
      t.mem = s.mem.writeW (addr x (7168 + q)) (BitVec.ofNat 8 v) := by
  refine Wp.wp_movi fun u₁ h₁ => ?_
  have k₁ := Proof.X25519.X86.updKeep h₁
  have c₁ := k₁.ctx hc
  refine scalar_store8 (by rw [c₁.edi]) (c₁.inW (by omega_using [hq]) (by decide))
    fun t ht => WP.block_nil ?_
  refine ⟨k₁.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩
  rw [ht.mem, h₁.mem]
  change s.mem.writeW _ ((u₁.gpr .eax).setWidth 8) = _
  rw [h₁.gpr]
  rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> rfl

theorem storeBit_saved {s₀ s : State} {x : BitVec 32} (hs : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hw : VG.Proof.X25519.X86.scR 8192 x ∈ s₀.wr) {q v : Nat} (hq : q < 256)
    (hv : v < 2) {f : Nat → Nat}
    (hb : ∀ k < 256, s.mem (addr x (7168 + k)) = BitVec.ofNat 8 (f k)) :
    WP isa (.block (storeBit q v)) s fun t => VG.Proof.Ed25519.X86.Saved s₀ x t ∧
      ∀ k < 256, t.mem (addr x (7168 + k)) = BitVec.ofNat 8 (if k = q then v else f k) := by
  refine WP.mono (VG.Proof.X25519.X86.Base.storeBit_ok (hs.ctx hx hw) hq hv) fun t ⟨kt, mt⟩ => ⟨?_, fun k hk => ?_⟩
  · refine hs.of_offset hx (Keep.scalar kt) (o := 7168 + q) (n := 1) ?_ (by omega_using [])
      (by omega_using [hq]) (by omega_using [hq])
    rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [mt]
    by_cases he : k = q
    · subst he; simp only [↓reduceIte]; exact bits_byte_write_self _ _ _
    · simp only [he, ↓reduceIte]
      rw [bits_byte_write_ne _ _ (by omega_using [hx, hk]) (by omega_using [hx, hq])
        (by omega_using [he])]
      exact hb k hk

theorem clampBits_ok {s₀ s : State} {x : BitVec 32} (hs : VG.Proof.Ed25519.X86.Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hw : VG.Proof.X25519.X86.scR 8192 x ∈ s₀.wr) {f : Nat → Nat}
    (hb : ∀ k < 256, s.mem (addr x (7168 + k)) = BitVec.ofNat 8 (f k)) :
    WP isa (.block clampBits) s fun t => VG.Proof.Ed25519.X86.Saved s₀ x t ∧
      ∀ k < 256, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (if k = 254 then 1 else if k = 255 then 0 else if k = 2 then 0 else if k = 1 then 0 else
          if k = 0 then 0 else f k) := by
  simp only [clampBits, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.Base.storeBit_saved hs hx hw (by decide) (by decide) hb)
    fun a ⟨ha, ba⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.Base.storeBit_saved ha hx hw (by decide) (by decide) ba)
    fun b ⟨hb', bb⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.Base.storeBit_saved hb' hx hw (by decide) (by decide) bb)
    fun c ⟨hc, bc⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.Base.storeBit_saved hc hx hw (by decide) (by decide) bc)
    fun d ⟨hd, bd⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.X86.Base.storeBit_saved hd hx hw (by decide) (by decide) bd) fun t ⟨ht, bt⟩ =>
    ⟨ht, fun k hk => ?_⟩
  rw [bt k hk]

/-! ## The u-coordinate -/

theorem uOps_eval (e : Env) : evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 :=
  ⟨rfl, rfl⟩

theorem uMul_eval (e : Env) : evalOps uMulOps e 0 = e 0 * e 15 := rfl

theorem uEncode_ok {x : BitVec 32} {s : State} (hc : Ed25519.X86.Ctx x s) :
    WP isa uEncode s fun t => IKeep x s t ∧
      VG.Proof.X25519.X86.fe t.mem x 64 = ((env s.mem x 2 + env s.mem x 1) *
        Spec.X25519.pow (env s.mem x 2 - env s.mem x 1) (Spec.X25519.P - 2)).val := by
  refine WP.seq (WP.mono (fieldCode_ok uOps hc) fun a ⟨ka, ea⟩ => ?_)
  have ca := (IKeep.of_field ka).ctx hc
  refine WP.seq (WP.mono (invert_spec x a ca) fun b ⟨kb, eb⟩ => ?_)
  have cb := kb.ctx ca
  refine WP.seq (WP.mono (fieldCode_ok uMulOps cb) fun c ⟨kc, ec⟩ => ?_)
  have cc := (IKeep.of_field kc).ctx cb
  refine WP.mono (freezeField_ok cc 0) fun t ⟨kt, _, vt⟩ => ?_
  refine ⟨(((IKeep.of_field ka).trans kb).trans (IKeep.of_field kc)).trans (IKeep.of_field kt), ?_⟩
  change VG.Proof.X25519.X86.fe t.mem x (offset 0) = _
  rw [vt, ec, VG.Proof.X25519.X86.Base.uMul_eval, eb, invEnv_eval, invEnv_x, ea, (VG.Proof.X25519.X86.Base.uOps_eval _).1, (VG.Proof.X25519.X86.Base.uOps_eval _).2,
    VG.Proof.X25519.invert_eq]

/-- The u-coordinate of a representative of `a`. -/
theorem u_rep {p : Spec.Ed25519.Point} {a : Ed25519.Edwards.EPoint Ed25519.dZ} (h : Rep p a) :
    Ed25519.toZ ((p.Z + p.Y) * Spec.X25519.pow (p.Z - p.Y) (Spec.X25519.P - 2)) =
      (1 + a.y) / (1 - a.y) := by
  rw [Ed25519.toZ_mul, Ed25519.toZ_pow, Ed25519.toZ_add, Ed25519.toZ_sub,
    Proof.X25519.Edwards.pow_P_sub_two, h.y, ← div_eq_mul_inv]
  have hz := h.z
  rw [show Ed25519.toZ p.Z + a.y * Ed25519.toZ p.Z = (1 + a.y) * Ed25519.toZ p.Z by ring,
    show Ed25519.toZ p.Z - a.y * Ed25519.toZ p.Z = (1 - a.y) * Ed25519.toZ p.Z by ring,
    mul_div_mul_right _ _ hz]

/-! ## The function -/

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.X25519.bytesAt m p 32 = Spec.Ed25519.bytesAt m p 32 :=
  rfl

/-- The bits of the decoded scalar, at byte 7168 of the workspace, and `d` in slot 16. -/
structure Ready (s₀ s : State) : Prop where
  saved : VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 2) s
  bits : ∀ q < 256, s.mem (addr (arg s₀ 2) (7168 + q)) = BitVec.ofNat 8
    ((Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32) /
      2 ^ q) % 2)
  d : env s.mem (arg s₀ 2) 16 = Spec.Ed25519.d

theorem scalar_length (s : State) :
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length = 32 := by
  simp [Spec.Ed25519.bytesAt]

theorem scalar_lt (s : State) : Spec.X25519.decodeScalar25519
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) < 2 ^ 256 := by
  have e := Proof.X25519.Edwards.decodeScalar25519_shift (VG.Proof.X25519.X86.Base.scalar_length s)
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by decide)] at e
  exact Nat.lt_trans e (by decide)

theorem start_ok {s : State} (h : x25519BaseLocal.pre s) :
    WP isa (.block x25519BaseStart) s (VG.Proof.X25519.X86.Base.Ready s) := by
  obtain ⟨hp, hi, _⟩ := scalarBase_pre h
  simp only [x25519BaseStart, List.append_assoc]
  refine WP.block_append (WP.mono (abiSave_ok hp) fun a ha => ?_)
  refine WP.block_append (WP.mono (inputBits_ok hp hi ha (by decide) (by decide))
    fun b ⟨hb, bits⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.Base.clampBits_ok hb hp.fit hp.wr
    (fun k hk => bits k (by omega_using [hk]))) fun b' ⟨hb', bits'⟩ => ?_)
  have cb := hb'.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  refine ⟨hb'.ikeep hp.fit (IKeep.of_field kc), fun q qq => ?_, by rw [ec, baseSetup_d]⟩
  rw [IKeep.bit (IKeep.of_field kc) cb q (by omega_using [qq]), bits' q qq,
    VG.Proof.X25519.X86.Base.clamp_bit (VG.Proof.X25519.X86.Base.scalar_length s) qq]

theorem comb_ok {s₀ s : State} (h : x25519BaseLocal.pre s₀) (hr : VG.Proof.X25519.X86.Base.Ready s₀ s) :
    WP isa combMultiply s fun t => Rep (point (env t.mem (arg s₀ 2)) 0 1 2 3)
      ((Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) •
        baseAff) ∧ VG.Proof.Ed25519.X86.Saved s₀ (arg s₀ 2) t := by
  obtain ⟨hp, _, _⟩ := scalarBase_pre h
  exact WP.mono (combMultiply_ok (hr.saved.ctx hp.fit hp.wr) (VG.Proof.X25519.X86.Base.scalar_lt s₀) hr.bits hr.d)
    fun t ⟨pt, kt⟩ => ⟨pt, hr.saved.mulkeep hp.fit kt⟩

theorem x25519Base_correct {s : State} (h : x25519BaseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ x25519BaseLocal.post s t := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h
  refine WP.seq (WP.mono (VG.Proof.X25519.X86.Base.start_ok h) fun c hc => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86.Base.comb_ok h hc) fun d ⟨pd, hd⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86.Base.uEncode_ok (hd.ctx hp.fit hp.wr)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 64) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.X25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) Spec.X25519.basePoint
  rw [VG.Proof.X25519.X86.Base.bytesAt_eq, VG.Proof.X25519.X86.Base.bytesAt_eq, et, ve,
    Proof.X25519.Edwards.x25519_basePoint (VG.Proof.X25519.X86.Base.scalar_length s) _ (VG.Proof.X25519.X86.Base.u_rep pd)]
  rfl

end VG.Proof.X25519.X86.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Base.Verified`. -/
section

/-!
# X25519 of the base point on x86: constant time, and the shared contract

Every piece's trace depends only on the pointers: the expansion and clamping
of the scalar store to fixed offsets of the workspace, the comb and the
inversion use only the workspace pointer (`combMultiply_ct`, the summaries of
`PointCTBlocks.lean`), and the output reloads its pointer from the stack.
-/

namespace VG.Proof.X25519.X86.Base

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86.Base
open VG.Proof.Ed25519.X86

theorem uEncode_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) uEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (regsTaint [.edi]) uEncode h).isSome = true := by
    taint_decide_sum [power250Sum, sqT1]
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ hc
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

theorem start_ct : RelCT isa
    (fun s t => x25519BaseLocal.pre s ∧ x25519BaseLocal.pre t ∧ x25519BaseLocal.pub s t)
    (.block x25519BaseStart) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht
  refine scalarTaint_agree (scalarTaint_wf ps os hs.2.1 hs.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.2.1 ht.2.2.2.2.1) sp ?_ (by decide) hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem finish_ct (s₀ t₀ : State) (hs : x25519BaseLocal.pre s₀) (ht : x25519BaseLocal.pre t₀)
    (hp : x25519BaseLocal.pub s₀ t₀) :
    RelCT isa (BaseSaved s₀ t₀) (.block (finishWords 64)) (fun _ _ => True) := by
  obtain ⟨ps, _, _⟩ := scalarBase_pre hs
  obtain ⟨pt, _, _⟩ := scalarBase_pre ht
  have loadct : RelCT isa (BaseSaved s₀ t₀)
      (.block [.mov .esi (.mem (Impl.X25519.X86.at_ .esp 4))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 64 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [finishWords, List.append_assoc]
  refine ctBlockAppend (hh.mono (fun _ _ h => h) ?_) tailct
  intro s t ⟨_, a, b, _, ha, hb⟩
  exact ⟨ha.1.edi.trans (hp.2.2.2.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

theorem tail_ct (s₀ t₀ : State) (hs : x25519BaseLocal.pre s₀) (ht : x25519BaseLocal.pre t₀)
    (hp : x25519BaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => VG.Proof.X25519.X86.Base.Ready s₀ s ∧ VG.Proof.X25519.X86.Base.Ready t₀ t)
      (.seq combMultiply (.seq uEncode (.block (finishWords 64)))) (fun _ _ => True) := by
  have mulct := combMultiply_ct.mono
    (P' := fun (s t : State) => VG.Proof.X25519.X86.Base.Ready s₀ s ∧ VG.Proof.X25519.X86.Base.Ready t₀ t)
    (fun _ _ h => h.1.saved.edi.trans (hp.2.2.2.trans h.2.saved.edi.symm)) (fun _ _ h => h)
  have mw (u s : State) (hu : x25519BaseLocal.pre u) (h : VG.Proof.X25519.X86.Base.Ready u s) :
      WP isa combMultiply s (VG.Proof.Ed25519.X86.Saved u (arg u 2)) :=
    WP.mono (VG.Proof.X25519.X86.Base.comb_ok hu h) fun _ ⟨_, kt⟩ => kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s hs h.1, mw t₀ t ht h.2⟩)
  have encct := uEncode_ct.mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => h.1.edi.trans (hp.2.2.2.trans h.2.edi.symm)) (fun _ _ h => h)
  have ew (u s : State) (hu : x25519BaseLocal.pre u) (h : VG.Proof.Ed25519.X86.Saved u (arg u 2) s) :
      WP isa uEncode s (VG.Proof.Ed25519.X86.Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (VG.Proof.X25519.X86.Base.uEncode_ok (h.ctx pu.fit pu.wr)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (VG.Proof.X25519.X86.Base.finish_ct s₀ t₀ hs ht hp))

theorem x25519Base_ct :
    ConstantTime isa x25519BaseLocal.pre x25519BaseLocal.pub x25519Base := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns VG.Proof.X25519.X86.Base.start_ct (fun _ _ h => ⟨VG.Proof.X25519.X86.Base.start_ok h.1, VG.Proof.X25519.X86.Base.start_ok h.2.1⟩)
  rw [x25519Base]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact VG.Proof.X25519.X86.Base.tail_ct u v hp.1 hp.2.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

theorem x25519Base_ok (s : State) (h : x25519BaseLocal.pre s) :
    ∃ tr t, Exec isa x25519Base s tr t ∧ abiPreserved s t ∧ x25519BaseLocal.post s t :=
  VG.Proof.X25519.X86.Base.x25519Base_correct h

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.X25519.X86.Base.satMem
  rd := [⟨0x2000, 32⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem x25519Base_verified :
    Verified X86.target x25519Base (Spec.X25519.x25519BaseContract X86.abi) :=
  Verified.of_correct VG.Proof.X25519.X86.Base.x25519Base_ok VG.Proof.X25519.X86.Base.x25519Base_ct (by
    have a0 : arg VG.Proof.X25519.X86.Base.satState 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.X25519.X86.Base.satState 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.X25519.X86.Base.satState 2 = 0x4000 := by decide
    have e : argAddr VG.Proof.X25519.X86.Base.satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, VG.Proof.X25519.X86.Base.x25519BaseLocal,
      scalarBaseLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using VG.Proof.X25519.X86.Base.satState)

end VG.Proof.X25519.X86.Base

end
