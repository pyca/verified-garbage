import VerifiedGarbage.Impl.X25519.X86.Base
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Spec.X25519.Contract

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
    WP isa (.block (storeBit q v)) s fun t => Keep s t ∧
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

theorem storeBit_saved {s₀ s : State} {x : BitVec 32} (hs : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hw : scR 8192 x ∈ s₀.wr) {q v : Nat} (hq : q < 256)
    (hv : v < 2) {f : Nat → Nat}
    (hb : ∀ k < 256, s.mem (addr x (7168 + k)) = BitVec.ofNat 8 (f k)) :
    WP isa (.block (storeBit q v)) s fun t => Saved s₀ x t ∧
      ∀ k < 256, t.mem (addr x (7168 + k)) = BitVec.ofNat 8 (if k = q then v else f k) := by
  refine WP.mono (storeBit_ok (hs.ctx hx hw) hq hv) fun t ⟨kt, mt⟩ => ⟨?_, fun k hk => ?_⟩
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

theorem clampBits_ok {s₀ s : State} {x : BitVec 32} (hs : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hw : scR 8192 x ∈ s₀.wr) {f : Nat → Nat}
    (hb : ∀ k < 256, s.mem (addr x (7168 + k)) = BitVec.ofNat 8 (f k)) :
    WP isa (.block clampBits) s fun t => Saved s₀ x t ∧
      ∀ k < 256, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (if k = 254 then 1 else if k = 255 then 0 else if k = 2 then 0 else if k = 1 then 0 else
          if k = 0 then 0 else f k) := by
  simp only [clampBits, List.append_assoc]
  refine WP.block_append (WP.mono (storeBit_saved hs hx hw (by decide) (by decide) hb)
    fun a ⟨ha, ba⟩ => ?_)
  refine WP.block_append (WP.mono (storeBit_saved ha hx hw (by decide) (by decide) ba)
    fun b ⟨hb', bb⟩ => ?_)
  refine WP.block_append (WP.mono (storeBit_saved hb' hx hw (by decide) (by decide) bb)
    fun c ⟨hc, bc⟩ => ?_)
  refine WP.block_append (WP.mono (storeBit_saved hc hx hw (by decide) (by decide) bc)
    fun d ⟨hd, bd⟩ => ?_)
  refine WP.mono (storeBit_saved hd hx hw (by decide) (by decide) bd) fun t ⟨ht, bt⟩ =>
    ⟨ht, fun k hk => ?_⟩
  rw [bt k hk]

/-! ## The u-coordinate -/

theorem uOps_eval (e : Env) : evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 :=
  ⟨rfl, rfl⟩

theorem uMul_eval (e : Env) : evalOps uMulOps e 0 = e 0 * e 15 := rfl

theorem uEncode_ok {x : BitVec 32} {s : State} (hc : Ed25519.X86.Ctx x s) :
    WP isa uEncode s fun t => IKeep x s t ∧
      fe t.mem x 64 = ((env s.mem x 2 + env s.mem x 1) *
        Spec.X25519.pow (env s.mem x 2 - env s.mem x 1) (Spec.X25519.P - 2)).val := by
  refine WP.seq (WP.mono (fieldCode_ok uOps hc) fun a ⟨ka, ea⟩ => ?_)
  have ca := (IKeep.of_field ka).ctx hc
  refine WP.seq (WP.mono (invert_spec x a ca) fun b ⟨kb, eb⟩ => ?_)
  have cb := kb.ctx ca
  refine WP.seq (WP.mono (fieldCode_ok uMulOps cb) fun c ⟨kc, ec⟩ => ?_)
  have cc := (IKeep.of_field kc).ctx cb
  refine WP.mono (freezeField_ok cc 0) fun t ⟨kt, _, vt⟩ => ?_
  refine ⟨(((IKeep.of_field ka).trans kb).trans (IKeep.of_field kc)).trans (IKeep.of_field kt), ?_⟩
  change fe t.mem x (offset 0) = _
  rw [vt, ec, uMul_eval, eb, invEnv_eval, invEnv_x, ea, (uOps_eval _).1, (uOps_eval _).2,
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
  saved : Saved s₀ (arg s₀ 2) s
  bits : ∀ q < 256, s.mem (addr (arg s₀ 2) (7168 + q)) = BitVec.ofNat 8
    ((Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32) /
      2 ^ q) % 2)
  d : env s.mem (arg s₀ 2) 16 = Spec.Ed25519.d

theorem scalar_length (s : State) :
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length = 32 := by
  simp [Spec.Ed25519.bytesAt]

theorem scalar_lt (s : State) : Spec.X25519.decodeScalar25519
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) < 2 ^ 256 := by
  have e := Proof.X25519.Edwards.decodeScalar25519_shift (scalar_length s)
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by decide)] at e
  exact Nat.lt_trans e (by decide)

theorem start_ok {s : State} (h : x25519BaseLocal.pre s) :
    WP isa (.block x25519BaseStart) s (Ready s) := by
  obtain ⟨hp, hi, _⟩ := scalarBase_pre h
  simp only [x25519BaseStart, List.append_assoc]
  refine WP.block_append (WP.mono (abiSave_ok hp) fun a ha => ?_)
  refine WP.block_append (WP.mono (inputBits_ok hp hi ha (by decide) (by decide))
    fun b ⟨hb, bits⟩ => ?_)
  refine WP.block_append (WP.mono (clampBits_ok hb hp.fit hp.wr
    (fun k hk => bits k (by omega_using [hk]))) fun b' ⟨hb', bits'⟩ => ?_)
  have cb := hb'.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  refine ⟨hb'.ikeep hp.fit (IKeep.of_field kc), fun q qq => ?_, by rw [ec, baseSetup_d]⟩
  rw [IKeep.bit (IKeep.of_field kc) cb q (by omega_using [qq]), bits' q qq,
    clamp_bit (scalar_length s) qq]

theorem comb_ok {s₀ s : State} (h : x25519BaseLocal.pre s₀) (hr : Ready s₀ s) :
    WP isa combMultiply s fun t => Rep (point (env t.mem (arg s₀ 2)) 0 1 2 3)
      ((Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) •
        baseAff) ∧ Saved s₀ (arg s₀ 2) t := by
  obtain ⟨hp, _, _⟩ := scalarBase_pre h
  exact WP.mono (combMultiply_ok (hr.saved.ctx hp.fit hp.wr) (scalar_lt s₀) hr.bits hr.d)
    fun t ⟨pt, kt⟩ => ⟨pt, hr.saved.mulkeep hp.fit kt⟩

theorem x25519Base_correct {s : State} (h : x25519BaseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ x25519BaseLocal.post s t := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h
  refine WP.seq (WP.mono (start_ok h) fun c hc => ?_)
  refine WP.seq (WP.mono (comb_ok h hc) fun d ⟨pd, hd⟩ => ?_)
  refine WP.seq (WP.mono (uEncode_ok (hd.ctx hp.fit hp.wr)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 64) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.X25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) Spec.X25519.basePoint
  rw [bytesAt_eq, bytesAt_eq, et, ve,
    Proof.X25519.Edwards.x25519_basePoint (scalar_length s) _ (u_rep pd)]
  rfl

end VG.Proof.X25519.X86.Base
