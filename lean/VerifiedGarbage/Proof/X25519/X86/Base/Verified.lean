module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.X25519.X86.Base.Lit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
meta import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Pow250Sum
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.X25519.X86.Base.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.X25519.X86.Base
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Impl.X25519.X86.Base
meta import VerifiedGarbage.Proof.X25519.Edwards.Ladder
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.Group.Extended
meta import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Tactic.Ring.RingNF
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring

/-! ### `X25519.X86.Base.Main`, which only this module used -/

section

/-!
# X25519 of the base point on x86: correctness

The scalar's bits are expanded and clamped (`clampBits_ok`: the bits of
`decodeScalar25519 k`), the comb computes a representative of `[k] B`
(`combMultiply_ok`), and `uEncode` its u-coordinate `(Z + Y) / (Z - Y)`,
which is `X25519(k, 9)` (`Proof/X25519/Edwards/Ladder.lean`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Base

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86.Base
open VG.Proof.Ed25519.X86
open VG.Proof.Ed25519 (Rep baseAff)

/-- The contract the proof is written against: `vg_ed25519_scalar_base`'s
precondition (the same arguments, and the comb's tables), with `X25519(k, 9)` as
postcondition. -/
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
  · have e := VG.Proof.X25519.scalar_bit hl (t := k) (by omega_using [hk, h255])
    simp only [Proof.X25519.bit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at e
    rw [e, VG.Proof.Ed25519.decodeLE_eq]
    have hb := VG.Proof.X25519.leNum_bit kb k
    simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb
    rw [hb]
    by_cases h3 : k < 3
    · rcases (by omega_using [h3] : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
    · by_cases h254 : k = 254
      · subst h254; rfl
      · have h2 : k ≠ 2 := by omega_using [h3]
        have h1 : k ≠ 1 := by omega_using [h3]
        have h0 : k ≠ 0 := by omega_using [h3]
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
  rcases (by omega_using [hv] : v = 0 ∨ v = 1) with rfl | rfl <;> rfl

theorem storeBit_saved {s₀ s : State} {x : BitVec 32} (hs : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hw : scR 8192 x ∈ s₀.wr) {q v : Nat} (hq : q < 256)
    (hv : v < 2) {f : Nat → Nat}
    (hb : ∀ k < 256, s.mem (addr x (7168 + k)) = BitVec.ofNat 8 (f k)) :
    WP isa (.block (storeBit q v)) s fun t => Saved s₀ x t ∧ Frame [sub x 7168 256] s.mem t.mem ∧
      ∀ k < 256, t.mem (addr x (7168 + k)) = BitVec.ofNat 8 (if k = q then v else f k) := by
  refine WP.mono (storeBit_ok (hs.ctx hx hw hs.stk) hq hv) fun t ⟨kt, mt⟩ => ⟨?_, ?_, fun k hk => ?_⟩
  · refine hs.of_offset hx (Keep.scalar kt) (o := 7168 + q) (n := 1) ?_ (by omega_using [])
      (by omega_using [hq]) (by omega_using [hq])
    rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (sub_contains (by omega_using [hx]) (by omega_using []) (by omega_using [hq]) (by decide))
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
    WP isa (.block clampBits) s fun t => Saved s₀ x t ∧ Frame [sub x 7168 256] s.mem t.mem ∧
      ∀ k < 256, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (if k = 254 then 1 else if k = 255 then 0 else if k = 2 then 0 else if k = 1 then 0 else
          if k = 0 then 0 else f k) := by
  simp only [clampBits, List.append_assoc]
  refine WP.block_append (WP.mono (storeBit_saved hs hx hw (by decide) (by decide) hb)
    fun a ⟨ha, fa, ba⟩ => ?_)
  refine WP.block_append (WP.mono (storeBit_saved ha hx hw (by decide) (by decide) ba)
    fun b ⟨hb', fb, bb⟩ => ?_)
  refine WP.block_append (WP.mono (storeBit_saved hb' hx hw (by decide) (by decide) bb)
    fun c ⟨hc, fc, bc⟩ => ?_)
  refine WP.block_append (WP.mono (storeBit_saved hc hx hw (by decide) (by decide) bc)
    fun d ⟨hd, fd, bd⟩ => ?_)
  refine WP.mono (storeBit_saved hd hx hw (by decide) (by decide) bd) fun t ⟨ht, ft, bt⟩ =>
    ⟨ht, (((fa.trans fb).trans fc).trans fd).trans ft, fun k hk => ?_⟩
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
  refine WP.seq (WP.mono (invert_ok ca) fun b ⟨kb, eb, el⟩ => ?_)
  have cb := kb.ctx ca
  refine WP.seq (WP.mono (fieldCode_ok uMulOps cb) fun c ⟨kc, ec⟩ => ?_)
  have cc := (IKeep.of_field kc).ctx cb
  refine WP.mono (freezeField_ok cc 0) fun t ⟨kt, _, vt⟩ => ?_
  refine ⟨(((IKeep.of_field ka).trans kb).trans (IKeep.of_field kc)).trans (IKeep.of_field kt), ?_⟩
  change fe t.mem x (offset 0) = _
  rw [vt, ec, uMul_eval, eb, el 0 (by decide), ea, (uOps_eval _).1, (uOps_eval _).2,
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
  ptr : wd s.mem (arg s₀ 2) combTbl = s₀.syms combSym
  tbl : TblAt (arg s₀ 2) (s₀.syms combSym) s
  tstk : (TBL ((s₀.syms combSym).setWidth 64)).Disjoint (callStk s)

theorem scalar_length (s : State) :
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length = 32 := by
  simp [Spec.Ed25519.bytesAt]

theorem scalar_lt (s : State) : Spec.X25519.decodeScalar25519
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) < 2 ^ 256 := by
  have e := Proof.X25519.Edwards.decodeScalar25519_shift (scalar_length s)
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (by decide)] at e
  exact Nat.lt_trans e (by decide)

theorem start_ok {s : State} (h : BodyPre s) :
    WP isa x25519BaseStart s (Ready s) := by
  obtain ⟨hr, hptr, htbl, hts⟩ := h
  obtain ⟨hp, hi, _⟩ := scalarBase_pre hr
  rw [x25519BaseStart]
  refine WP.seq (WP.mono (abiSave_frame hp) fun a ⟨ha, fa⟩ => ?_)
  refine WP.seq (WP.mono (inputBits_frame hp hi ha (by decide) (by decide) (by decide))
    fun b ⟨hb, fb, bits⟩ => ?_)
  refine WP.block_append (WP.mono (clampBits_ok hb hp.fit hp.wr
    (fun k hk => bits k (by omega_using [hk]))) fun b' ⟨hb', fb', bits'⟩ => ?_)
  have cb := hb'.ctx hp.fit hp.wr hp.stk
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb'.ikeep hp.fit (IKeep.of_field kc)
  have toScr : ∀ {m m' : Mem} {o n : Nat}, Frame [sub (arg s 2) o n] m m' → o + n ≤ 8192 → o < 8192 →
      Frame [scR 8192 (arg s 2)] m m' := fun f h1 h2 => f.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, by rw [scR_eq]; exact sub_sub hp.fit (Nat.zero_le _) h1 h2⟩
  refine ⟨hc, fun q qq => ?_, by rw [ec, baseSetup_d], ?_,
    htbl.of_frame hc.rd ((((toScr fa (by decide) (by decide)).trans (toScr fb (by decide) (by decide))).trans
      (toScr fb' (by decide) (by decide))).trans (toScr kc.frame (by decide) (by decide))) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h, by rw [callStk, hc.esp]; exact hts⟩
  · rw [IKeep.bit (IKeep.of_field kc) cb q (by omega_using [qq]), bits' q qq,
      clamp_bit (scalar_length s) qq]
  · rw [wd_frame1 kc.frame hp.fit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 fb' hp.fit (by decide) (by decide) (Or.inl (by decide)),
      wd_frame1 fb hp.fit (by decide) (by decide) (Or.inl (by decide)),
      wd_frame1 fa hp.fit (by decide) (by decide) (Or.inr (by decide))]
    exact hptr

theorem comb_ok {s₀ s : State} (h : BaseRegions s₀) (hr : Ready s₀ s) :
    WP isa combMultiply s fun t => Rep (point (env t.mem (arg s₀ 2)) 0 1 2 3)
      ((Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) •
        baseAff) ∧ Saved s₀ (arg s₀ 2) t := by
  obtain ⟨hp, _, _⟩ := scalarBase_pre h
  exact WP.mono (combMultiply_ok (hr.saved.ctx hp.fit hp.wr hp.stk) (scalar_lt s₀) hr.bits hr.d hr.ptr hr.tbl hr.tstk)
    fun t ⟨pt, kt⟩ => ⟨pt, hr.saved.mulkeep hp.fit kt⟩

theorem x25519BaseBody_correct {s : State} (h : BodyPre s) :
    WP isa x25519BaseBody s fun t => abiPreserved s t ∧ x25519BaseLocal.post s t := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h.1
  rw [x25519BaseBody]
  refine WP.seq (WP.mono (start_ok h) fun c hc => ?_)
  refine WP.seq (WP.mono (comb_ok h.1 hc) fun d ⟨pd, hd⟩ => ?_)
  refine WP.seq (WP.mono (uEncode_ok (hd.ctx hp.fit hp.wr hp.stk)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 64) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.X25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) Spec.X25519.basePoint
  rw [bytesAt_eq, bytesAt_eq, et, ve,
    Proof.X25519.Edwards.x25519_basePoint (scalar_length s) _ (u_rep pd)]
  rfl

theorem x25519Base_correct {s : State} (h : x25519BaseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ x25519BaseLocal.post s t := by
  rw [x25519Base]
  refine WP.seq (WP.mono (combAddr_ok h) fun s₁ P => ?_)
  refine WP.mono (x25519BaseBody_correct P.pre) fun t ⟨ha, hq⟩ => ⟨P.abi ha, ?_⟩
  change Spec.X25519.bytesAt t.mem ((arg s₁ 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s₁.mem ((arg s₁ 1).setWidth 64) 32)
      Spec.X25519.basePoint at hq
  change Spec.X25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) Spec.X25519.basePoint
  rw [P.args 0 (by decide), P.args 1 (by decide), bytesAt_eq s₁.mem, P.input] at hq
  exact hq

end VG.Proof.X25519.X86.Base

end

end

/-!
# X25519 of the base point on x86: constant time, and the shared contract

Every piece's trace depends only on the pointers: the static's address, its
frame below `esp` and its store to the workspace (`combAddr_ct`), the expansion
and clamping of the scalar store to fixed offsets of the workspace, the comb and
the inversion use only the workspace pointer and the static's address
(`combMultiply_ct`, `uEncode_ct`), and the output
reloads its pointer from the stack.
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Base

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86.Base
open VG.Proof.Ed25519.X86

theorem uEncode_ct {x : BitVec 32} : RelCT isa (CallCTPre x) uEncode (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check callTaint₀ uEncode h).isSome = true := by
    taint_decide_sum [VG.Proof.X25519.X86.pow250Sum]
  exact VG.RelCT.taint (A := taint) callTaint₀ (fun _ _ h => callTaint₀_agree h) hc

theorem start_ct : RelCT isa
    (fun s t => BodyPre s ∧ BodyPre t ∧ x25519BaseLocal.pub s t)
    x25519BaseStart (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2, _⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs.1
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht.1
  refine scalarTaint_agree (scalarTaint_wf ps os hs.1.2.1 hs.1.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.1.2.1 ht.1.2.2.2.2.1) sp ?_ (by decide) hs.1.2.1 ht.1.2.1 ps.sp_fit
    pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem finish_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
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
  exact ⟨ha.1.edi.trans (hp.2.2.2.1.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

theorem tail_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
    (hp : x25519BaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => Ready s₀ s ∧ Ready t₀ t)
      (.seq combMultiply (.seq uEncode (.block (finishWords 64)))) (fun _ _ => True) := by
  have mulct := (combMultiply_ct (x := arg s₀ 2)).mono
    (P' := fun (s t : State) => Ready s₀ s ∧ Ready t₀ t)
    (fun s t h => by
      have ht' := pointCTCtx_saved ht h.2.saved
      rw [← hp.2.2.2.1] at ht'
      refine ⟨pointCTCtx_saved hs h.1.saved, ht', ?_, ?_, ?_⟩
      · rw [h.1.saved.wr, h.2.saved.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1]
      · rw [h.1.saved.esp, h.2.saved.esp, hp.1]
      · rw [h.1.ptr, hp.2.2.2.1, h.2.ptr, hp.2.2.2.2]) (fun _ _ h => h)
  have mw (u s : State) (hu : BaseRegions u) (h : Ready u s) :
      WP isa combMultiply s (Saved u (arg u 2)) :=
    WP.mono (comb_ok hu h) fun _ ⟨_, kt⟩ => kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s hs h.1, mw t₀ t ht h.2⟩)
  have encct := (uEncode_ct (x := arg s₀ 2)).mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => by
      have ct := pointCTCtx_saved ht h.2
      rw [← hp.2.2.2.1] at ct
      exact ⟨pointCTCtx_saved hs h.1, ct, by rw [h.1.wr, h.2.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1],
        by rw [h.1.esp, h.2.esp, hp.1]⟩) (fun _ _ h => h)
  have ew (u s : State) (hu : BaseRegions u) (h : Saved u (arg u 2) s) :
      WP isa uEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (uEncode_ok (h.ctx pu.fit pu.wr pu.stk)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (finish_ct s₀ t₀ hs ht hp))

theorem x25519BaseBody_ct : RelCT isa
    (fun s t => BodyPre s ∧ BodyPre t ∧ x25519BaseLocal.pub s t) x25519BaseBody (fun _ _ => True) := by
  have start := ctWithRuns start_ct (fun _ _ h => ⟨start_ok h.1, start_ok h.2.1⟩)
  rw [x25519BaseBody]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact tail_ct u v hp.1.1 hp.2.1.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

theorem x25519Base_ct :
    ConstantTime isa x25519BaseLocal.pre x25519BaseLocal.pub x25519Base := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have pro := ctWithRuns combAddr_ct (fun _ _ h => ⟨combAddr_ok h.1, combAddr_ok h.2.1⟩)
  rw [x25519Base]
  refine VG.RelCT.seq pro ?_
  intro s t ts tt s' t' ⟨_, u, v, ⟨_, _, hp⟩, Pu, Pv⟩ es et
  exact x25519BaseBody_ct _ _ _ _ _ _ ⟨Pu.pre, Pv.pre, Prologue.pub Pu Pv hp⟩ es et

theorem x25519Base_ok (s : State) (h : x25519BaseLocal.pre s) :
    ∃ tr t, Exec isa x25519Base s tr t ∧ abiPreserved s t ∧ x25519BaseLocal.post s t :=
  x25519Base_correct h

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith satArgs
  rd := [⟨0x2000, 32⟩, ⟨0x8004, 12⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem sat_arg (j : Nat) (hj : j < 3) : arg satState j = satArgs.readW (argAddr satState j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith satArgs _ = _
  rw [satMemWith_out]
  have : ∀ j < 3, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr satState j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega_using [hb])

theorem x25519Base_sat :
    (Spec.X25519.x25519BaseContract (X86.abi.withConsts combConsts) 8).pre satState := by
  have hl := combWords_length
  have a0 : arg satState 0 = 0x1000 := (sat_arg 0 (by decide)).trans (by decide)
  have a1 : arg satState 1 = 0x2000 := (sat_arg 1 (by decide)).trans (by decide)
  have a2 : arg satState 2 = 0x4000 := (sat_arg 2 (by decide)).trans (by decide)
  have held : TblWords ((satState.syms combSym).setWidth 64) satState.mem := satMemWith_held satArgs
  generalize e : satState = s
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, by rw [hl]; rfl, held, by rw [hl]; decide, ?_, ?_, ?_, by decide, ?_⟩
  · rw [hl]
    intro r hr
    change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [hl]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem x25519Base_implies :
    x25519BaseLocal.Implies (Spec.X25519.x25519BaseContract (X86.abi.withConsts combConsts) 8) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨h4, hsp, hd, held, hfit, hdw, -, hstk, -, ht, hw, -, o2, o3, i2, s3, r0, -, r2, -,
      b0, b1, b2, -, f0, f1, f2⟩ := h
    have be : callStk s = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩ := below_eq (sp := s.gpr .esp) h4
    refine ⟨⟨?_, hw, o2, i2, o3.symm, s3.symm, r0, r2, f0, f1, f2, by omega_using [hsp], h4, by rw [be]; exact b1,
      by rw [be]; exact b2, by rw [be]; exact b0⟩, by rw [be]; exact b0, held, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · rw [be]; exact hstk
  post := by
    intro s t _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq, Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨satState, x25519Base_sat⟩

theorem x25519Base_verified :
    Verified X86.target x25519Base (Spec.X25519.x25519BaseContract (X86.abi.withConsts combConsts) 8) :=
  Verified.of_correct x25519Base_ok x25519Base_ct x25519Base_implies

end VG.Proof.X25519.X86.Base
