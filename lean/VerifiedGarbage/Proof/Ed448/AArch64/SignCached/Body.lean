module

public import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Entry
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
public import VerifiedGarbage.Proof.X448.AArch64.Base.Comb
public import VerifiedGarbage.Spec.Ed448.Contract

import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
/-!
# Ed448 signing with a cached public key on AArch64: the frame's entry

The saved arguments (`Args`) as the body reads them (`arg_src`), the inputs'
bytes as on entry (`in_bytes`), and the entry, which keeps `len` and
`scratch` and writes the header of `dom4` in the locals (`entry_ok`).
-/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/SignCached/Layout.lean`, which only this module imported.
section

/-!
# Ed448 signing with a cached public key on AArch64: where everything is

The contract the proof is written against (`scLocal`: the facts of
`Spec.Ed448.signCachedContract` for 352 bytes of stack, stated for AArch64),
and the layout of a call (`Lay`): the buffers, the frame's base `E`, and the
`Env` of the frame's body, which keeps `len`, `scratch` and the header of
`dom4` in its locals.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Proof.Ed448.AArch64.Whole (Env sigWord TBL)
open VG.Impl.X448.AArch64.Base (combSym combWords)
open VG.Proof.X448.AArch64.Base (CombHeld)
open VG.Proof.Ed25519.AArch64.Whole (FR ARGS CK)

/-- `vg_ed448_sign_cached(out = x0, seed = x1, pk = x2, context = x3,
ctxlen = x4, message = x5, len = x6, scratch = x7)`, with 352 bytes of stack. -/
def scLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 114⟩
    let seed : Region := ⟨s.gpr .x1, 57⟩
    let pk : Region := ⟨s.gpr .x2, 57⟩
    let ctx : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let msg : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
    let scr : Region := ⟨s.gpr .x7, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed, pk, ctx, msg, TBL (s.syms combSym)] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint ctx ∧ out.Disjoint msg ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧
      stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 114 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧
      Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) ∧
      (s.gpr .x4).toNat ≤ 255 ∧ CombHeld s [out, scr, stk]
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .x0) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) (Spec.Ed448.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.gpr .x7 = t.gpr .x7 ∧ s.syms combSym = t.syms combSym

structure Lay where
  out : Addr
  seed : Addr
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  scr : Addr
  E : Addr
  /-- The comb's tables (the static `combSym`), which `vg_ed448_scalar_base` reads. -/
  T : Addr

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 114⟩
abbrev SEED : Region := ⟨L.seed, 57⟩
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.E, 336⟩
abbrev TB : Region := TBL L.T

/-- The saved argument `j`. -/
def arg (j : Nat) : Addr :=
  match j with | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.ctx | 4 => L.ctxLen | _ => L.msg

def inputs : List Region := [L.SEED, L.PK, L.CTX, L.MSG, L.TB]

/-- The frame's body: it reads the inputs and the saved arguments, writes
`out` and `scratch`, and keeps `len`, `scratch` and the header of `dom4` in
its locals. -/
def env : Env where
  E := L.E
  ins := L.inputs ++ [ARGS L.E]
  outs := [L.OUT, L.SCR]
  ls := [(fLen, L.len), (fScr, L.scr), (fHdr, sigWord), (fHdr + 8, L.ctxLen <<< 8)]
  T := L.T
  sym := VG.Impl.X448.AArch64.Base.combSym
  words := VG.Impl.X448.AArch64.Base.combWords

structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  op : L.OUT.Disjoint L.PK
  ox : L.OUT.Disjoint L.CTX
  om : L.OUT.Disjoint L.MSG
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  pc : L.PK.Disjoint L.SCR
  xc : L.CTX.Disjoint L.SCR
  mc : L.MSG.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kp : L.STK.Disjoint L.PK
  kx : L.STK.Disjoint L.CTX
  km : L.STK.Disjoint L.MSG
  kc : L.STK.Disjoint L.SCR
  co : (CK L.E).Disjoint L.OUT
  cs : (CK L.E).Disjoint L.SEED
  cp : (CK L.E).Disjoint L.PK
  cx : (CK L.E).Disjoint L.CTX
  cm : (CK L.E).Disjoint L.MSG
  cc : (CK L.E).Disjoint L.SCR
  no : L.out.toNat + 114 ≤ 2 ^ 64
  ns : L.seed.toNat + 57 ≤ 2 ^ 64
  np : L.pk.toNat + 57 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  cl : L.ctxLen.toNat < 256
  tbo : L.TB.Disjoint L.OUT
  tbc : L.TB.Disjoint L.SCR
  tbk : L.TB.Disjoint L.STK
  tbck : L.TB.Disjoint (CK L.E)
  tbfit : L.T.toNat + 8 * combWords.length ≤ 2 ^ 64

end Lay

theorem frame_sub (L : Lay) : Region.Sub (FR L.E) L.STK := Region.sub_prefix (by decide : 256 ≤ 336)

attribute [local irreducible] VG.Impl.X448.AArch64.Base.combWords

theorem env_ok {L : Lay} (hL : L.Ok) : L.env.Ok where
  args := by simp [Lay.env]
  ls := by simp [Lay.env, fLen, fScr, fHdr]
  fo := by
    intro R hR
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hL.ko.sub_left (frame_sub L)
    · exact hL.kc.sub_left (frame_sub L)
  co := by
    intro R hR
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hL.co
    · exact hL.cc
  e16 := hL.e16
  tin := by simp [Lay.env, Lay.inputs]
  tfr := hL.tbk.sub_right (frame_sub L)
  tck := hL.tbck
  tout := by
    intro R hR
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [hL.tbo, hL.tbc]
  tfit := hL.tbfit

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    VG.Proof.Ed25519.AArch64.Whole.base s, s.syms combSym⟩

theorem lay_ok {s : State} (h : scLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, op, ox, om, oc, sc, pc, xc, mc, ko, ks, kp, kx, km, kc, no, ns, np, nc, hsp, _, hc,
    -, fit, dj⟩ := h
  have st := VG.Proof.Ed25519.AArch64.Whole.stk_sub s
  have ck := VG.Proof.Ed25519.AArch64.Whole.ck_sub s
  have dk := dj (below s.sp 352) (by simp)
  exact ⟨os, op, ox, om, oc, sc, pc, xc, mc, ko.sub_left st, ks.sub_left st, kp.sub_left st, kx.sub_left st,
    km.sub_left st, kc.sub_left st, ko.sub_left ck, ks.sub_left ck, kp.sub_left ck, kx.sub_left ck,
    km.sub_left ck, kc.sub_left ck, no, ns, np, nc, VG.Proof.Ed25519.AArch64.Whole.base_16 hsp,
    show (s.gpr .x4).toNat < 256 by omega, dj ⟨s.gpr .x0, 114⟩ (by simp), dj ⟨s.gpr .x7, 8192⟩ (by simp),
    dk.sub_right st,
    dk.sub_right ck, fit⟩

end VG.Proof.Ed448.AArch64.SignCached
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS keep hdr)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue readW_eq_read)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The saved arguments, and the comb's words. -/
def Args (L : Lay) (m : Mem) : Prop :=
  (∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.arg j) ∧
    VG.Proof.Ed448.AArch64.Whole.TblWords L.T m

abbrev Ctx0 (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.env.ins L.env.outs t

theorem args_sub (L : Lay) : Region.Sub (ARGS L.E) L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- What the body may write misses the saved arguments. -/
theorem args_apart (hL : L.Ok) : ∀ r ∈ L.env.outs ++ [FR L.E, CK L.E], (ARGS L.E).Disjoint r := by
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

theorem arg_word (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) {j : Nat} (hj : j < 6) :
    t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * j)) 8 = L.arg j := by
  rw [← readW_eq_read, ← ha.1 j hj]
  exact hc.frame.readW (r := ARGS L.E) (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega)
    (by decide)) (args_apart hL) (by decide)

theorem arg_src (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) {j : Nat} (hj : j < 6)
    (x0 : BitVec 64) : srcValue L.E t.mem x0 (.val (.caller j 0)) = L.arg j := by
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value]
  rw [arg_word hL hc ha hj, BitVec.add_zero]

/-- An input's bytes, as on entry. -/
theorem in_bytes (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) {R : Region} (hR : R ∈ L.inputs)
    {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt t.mem R.base n = Spec.Sha3.bytesAt m₀ R.base n := by
  unfold Spec.Sha3.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := R) ?_ hl (by
    have := List.mem_range.mp hi; omega)
  simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hR
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) <;> rcases hR with rfl | rfl | rfl | rfl | rfl
  exacts [hL.os.symm, hL.op.symm, hL.ox.symm, hL.om.symm, hL.tbo, hL.sc, hL.pc, hL.xc, hL.mc, hL.tbc,
    (hL.ks.sub_left (frame_sub L)).symm, (hL.kp.sub_left (frame_sub L)).symm,
    (hL.kx.sub_left (frame_sub L)).symm, (hL.km.sub_left (frame_sub L)).symm,
    hL.tbk.sub_right (frame_sub L), hL.cs.symm, hL.cp.symm, hL.cx.symm, hL.cm.symm, hL.tbck]

/-- `len` and `scratch` kept, and the header of `dom4`. -/
theorem entry_ok (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.len)
    (h7 : t.gpr .x7 = L.scr) (hsy : t.syms Impl.X448.AArch64.Base.combSym = L.T) :
    WP isa (.block entry) t fun u => WCtx L.env g vec m₀ u := by
  have hfr : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x6) (d := fLen) (by decide)
    ⟨_, hfr, Offset.contains_base _ (by decide) (by decide)⟩) fun a ⟨ka, _, am⟩ sa => ?_
  have hfa : (⟨a.sp, 256⟩ : Region) ∈ a.wr := by rw [ka.sp, ka.wr]; exact hfr
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x7) (d := fScr) (by decide)
    ⟨_, hfa, Offset.contains_base _ (by decide) (by decide)⟩) fun b ⟨kb, _, bm⟩ sb => ?_
  have hfb : (⟨b.sp, 256⟩ : Region) ∈ b.wr := by rw [kb.sp, kb.wr]; exact hfa
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.hdr_ok (d := fHdr) (j := 4) (by decide) (by decide) hfb (by
    rw [kb.rd, kb.wr, ka.rd, ka.wr, kb.sp, ka.sp, hc.rd, hc.wr, hc.sp]
    exact ⟨ARGS L.E, List.mem_append_left _ (by simp [Lay.env]),
      Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)⟩)) fun u ⟨ku, um⟩ su => ?_
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x15), h6, hc.sp] at am
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x15), ka.regs .x7 (by decide) (by decide), h7,
    ka.sp, hc.sp] at bm
  rw [kb.sp, ka.sp, hc.sp] at um
  have hread : b.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 4)) 8 = L.ctxLen := by
    rw [bm, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
      am, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))]
    exact arg_word hL hc ha (j := 4) (by decide)
  rw [hread] at um
  have hf : Frame [FR L.E] t.mem u.mem := by
    rw [um, bm, am]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_)
      |>.writeW (List.mem_singleton_self _) _ ?_) |>.writeW (List.mem_singleton_self _) _ ?_
    all_goals exact Offset.contains_base _ (by decide) (by decide)
  refine ⟨hc.of_frame (ku.rd.trans (kb.rd.trans ka.rd)) (ku.wr.trans (kb.wr.trans ka.wr))
    (ku.sp.trans (kb.sp.trans ka.sp)) (fun r hr _ => ?_)
    (fun r _ => by rw [ku.v, kb.v, ka.v]) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl fun _ h => h),
    ?_, by rw [su, sb, sa]; exact hsy⟩
  · rw [ku.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr),
      kb.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr),
      ka.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)]
  · intro p hp
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · show u.mem.read (L.E + BitVec.ofNat 64 fLen) 8 = L.len
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)), bm,
        VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)), am,
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 fScr) 8 = L.scr
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)), bm,
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 fHdr) 8 = sigWord
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 (fHdr + 8)) 8 = L.ctxLen <<< 8
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_self]

end VG.Proof.Ed448.AArch64.SignCached
