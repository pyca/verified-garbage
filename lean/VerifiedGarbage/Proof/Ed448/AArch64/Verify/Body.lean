module

public import VerifiedGarbage.Impl.Ed448.AArch64.Verify
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Entry
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Static
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
# Ed448 verification on AArch64: the frame's body

From the saved arguments (`Args`) and `scratch` in `x6`: the entry keeps
`scratch` and the header of `dom4` in the locals (`entry_ok`), the hash
`H(dom4(0, C) ‖ R ‖ A ‖ M)` is squeezed into the locals (`hash_ok`), reduced
into `k` (`reduce_step`), and `x0` is the verification equation's result
(`body_ok`).
-/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Verify/Layout.lean`, which only this module imported.
section

/-!
# Ed448 verification on AArch64: where everything is

The contract the proof is written against (`vLocal`: the facts of
`Spec.Ed448.verifyContract` for 352 bytes of stack, stated for AArch64), and
the layout of a call (`Lay`): the buffers, the frame's base `E`, and the
`Env` of the frame's body, which keeps `scratch` and the header of `dom4` in
its locals.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Proof.Ed448.AArch64.Whole (Env WCtx sigWord TBL)
open VG.Impl.Ed448.AArch64.Sparse (baseSym baseWords)
open VG.Proof.Ed448.AArch64.Sparse (BaseHeld)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

/-- Public verification inputs, as permitted by the reviewed API leak. -/
def PublicBytes (s t:State) : Prop :=
  Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57=Spec.Ed448.bytesAt t.mem (t.gpr .x0) 57 ∧
  Spec.Ed448.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat=
    Spec.Ed448.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat ∧
  Spec.Ed448.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat=
    Spec.Ed448.bytesAt t.mem (t.gpr .x3) (t.gpr .x4).toNat ∧
  Spec.Ed448.bytesAt s.mem (s.gpr .x5) 114=Spec.Ed448.bytesAt t.mem (t.gpr .x5) 114

/-- `vg_ed448_verify(pk = x0, context = x1, ctxlen = x2, message = x3, len = x4,
signature = x5, scratch = x6)`, with 352 bytes of stack. -/
def vLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0, 57⟩
    let ctx : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let msg : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let sig : Region := ⟨s.gpr .x5, 114⟩
    let scr : Region := ⟨s.gpr .x6, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [pk, ctx, msg, sig, TBL (s.syms baseSym) baseWords] ∧ s.wr = [scr] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 114 ≤ 2 ^ 64 ∧
      (s.gpr .x6).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧ BaseHeld s [scr, stk]
  post s t := t.gpr .x0 = if Spec.Ed448.verify (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x5) 114) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.syms baseSym = t.syms baseSym ∧ PublicBytes s t

structure Lay where
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  sig : Addr
  scr : Addr
  E : Addr
  /-- The comb's tables (the static `baseSym`), which `vg_ed448_verify_equation` reads. -/
  T : Addr

namespace Lay
variable (L : Lay)
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig, 114⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.E, 336⟩
abbrev TB : Region := TBL L.T baseWords

/-- The saved argument `j`. -/
def arg (j : Nat) : Addr :=
  match j with | 0 => L.pk | 1 => L.ctx | 2 => L.ctxLen | 3 => L.msg | 4 => L.len | _ => L.sig

def inputs : List Region := [L.PK, L.CTX, L.MSG, L.SIG, L.TB]

/-- The frame's body: it reads the inputs and the saved arguments, writes
`scratch`, and keeps `scratch` and the header of `dom4` in its locals. -/
def env : Env where
  E := L.E
  ins := L.inputs ++ [ARGS L.E]
  outs := [L.SCR]
  ls := [(fScr, L.scr), (fHdr, sigWord), (fHdr + 8, L.ctxLen <<< 8)]
  T := L.T
  sym := baseSym
  words := baseWords

structure Ok : Prop where
  pc : L.PK.Disjoint L.SCR
  cc : L.CTX.Disjoint L.SCR
  mc : L.MSG.Disjoint L.SCR
  sc : L.SIG.Disjoint L.SCR
  kp : L.STK.Disjoint L.PK
  kx : L.STK.Disjoint L.CTX
  km : L.STK.Disjoint L.MSG
  ks : L.STK.Disjoint L.SIG
  kc : L.STK.Disjoint L.SCR
  cp : (CK L.E).Disjoint L.PK
  cx : (CK L.E).Disjoint L.CTX
  cm : (CK L.E).Disjoint L.MSG
  cs : (CK L.E).Disjoint L.SIG
  ck : (CK L.E).Disjoint L.SCR
  np : L.pk.toNat + 57 ≤ 2 ^ 64
  ns : L.sig.toNat + 114 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  cl : L.ctxLen.toNat < 256
  tbc : L.TB.Disjoint L.SCR
  tbk : L.TB.Disjoint L.STK
  tbck : L.TB.Disjoint (CK L.E)
  tbfit : L.T.toNat + 8 * baseWords.length ≤ 2 ^ 64

end Lay

theorem frame_sub (L : Lay) : Region.Sub (FR L.E) L.STK := Region.sub_prefix (by decide : 256 ≤ 336)

attribute [local irreducible] baseWords VG.Impl.X448.AArch64.Base.combWords

theorem env_ok {L : Lay} (hL : L.Ok) : L.env.Ok:=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact List.mem_append_right _ (List.mem_singleton_self _)
  · simp [Lay.env, fScr, fHdr]
  ·
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.kc.sub_left (frame_sub L)
  ·
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.ck
  · exact hL.e16
  · exact List.mem_append_left _ (List.mem_of_getElem? (i:=4) rfl)
  ·
    change L.TB.Disjoint (FR L.E)
    exact hL.tbk.sub_right (frame_sub L)
  · change L.TB.Disjoint (CK L.E);exact hL.tbck
  ·
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.tbc
  · change L.T.toNat+8*baseWords.length≤2^64;exact hL.tbfit

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6,
    VG.Proof.Ed25519.AArch64.Whole.base s, s.syms baseSym⟩

theorem lay_ok {s : State} (h : vLocal.pre s) (hc : (s.gpr .x2).toNat < 256) : (lay s).Ok := by
  obtain ⟨_, _, pc, cc, mc, sc, kp, kx, km, ks, kc, np, ns, nc, hsp, -, fit, dj⟩ := h
  have st := VG.Proof.Ed25519.AArch64.Whole.stk_sub s
  have ck := VG.Proof.Ed25519.AArch64.Whole.ck_sub s
  have dk := dj (below s.sp 352) (by simp)
  exact ⟨pc, cc, mc, sc, kp.sub_left st, kx.sub_left st, km.sub_left st, ks.sub_left st, kc.sub_left st,
    kp.sub_left ck, kx.sub_left ck, km.sub_left ck, ks.sub_left ck, kc.sub_left ck, np, ns, nc,
    VG.Proof.Ed25519.AArch64.Whole.base_16 hsp, hc, dj ⟨s.gpr .x6, 8192⟩ (by simp), dk.sub_right st,
    dk.sub_right ck, fit⟩

end VG.Proof.Ed448.AArch64.Verify
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS keep hdr)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue readW_eq_read)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The saved arguments, and the comb's words. -/
def Args (L : Lay) (m : Mem) : Prop :=
  (∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.arg j) ∧
    VG.Proof.Ed448.AArch64.Whole.TblWords L.T m VG.Impl.Ed448.AArch64.Sparse.baseWords

abbrev Ctx0 (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.env.ins L.env.outs t

theorem args_sub (L : Lay) : Region.Sub (ARGS L.E) L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- What the body may write misses the saved arguments. -/
theorem args_apart (hL : L.Ok) : ∀ r ∈ L.env.outs ++ [FR L.E, CK L.E], (ARGS L.E).Disjoint r := by
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
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
  rintro r (rfl | rfl | rfl) <;> rcases hR with rfl | rfl | rfl | rfl | rfl
  exacts [hL.pc, hL.cc, hL.mc, hL.sc, hL.tbc, (hL.kp.sub_left (frame_sub L)).symm,
    (hL.kx.sub_left (frame_sub L)).symm, (hL.km.sub_left (frame_sub L)).symm,
    (hL.ks.sub_left (frame_sub L)).symm, hL.tbk.sub_right (frame_sub L), hL.cp.symm, hL.cx.symm,
    hL.cm.symm, hL.cs.symm, hL.tbck]

/-- `scratch` kept, and the header of `dom4`. -/
theorem entry_ok (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.scr)
    (hsy : t.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T) :
    WP isa (.block entry) t fun u => WCtx L.env g vec m₀ u := by
  have hfr : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  rw [entry, WP.block_append_iff]
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x6) (d := fScr) (by decide)
    ⟨_, hfr, Offset.contains_base _ (by decide) (by decide)⟩) fun a ⟨ka, _, am⟩ sa => ?_
  have hfa : (⟨a.sp, 256⟩ : Region) ∈ a.wr := by rw [ka.sp, ka.wr]; exact hfr
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.Whole.hdr_ok (d := fHdr) (j := 2) (by decide) (by decide) hfa (by
    rw [ka.rd, ka.wr, ka.sp, hc.rd, hc.wr, hc.sp]
    exact ⟨ARGS L.E, List.mem_append_left _ (by simp [Lay.env]),
      Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)⟩)) fun u ⟨ku, um⟩ su => ?_
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x15), h6, hc.sp] at am
  rw [ka.sp, hc.sp] at um
  have hread : a.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 2)) 8 = L.ctxLen := by
    rw [am, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))]
    exact arg_word hL hc ha (j := 2) (by decide)
  rw [hread] at um
  have hf : Frame [FR L.E] t.mem u.mem := by
    rw [um, am]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_)
      |>.writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base _ (by decide) (by decide)
    · exact Offset.contains_base _ (by decide) (by decide)
    · exact Offset.contains_base _ (by decide) (by decide)
  refine ⟨hc.of_frame (ku.rd.trans ka.rd) (ku.wr.trans ka.wr) (ku.sp.trans ka.sp) (fun r hr _ => ?_)
    (fun r _ => by rw [ku.v, ka.v]) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl fun _ h => h),
    ?_, by rw [su, sa]; exact hsy⟩
  · rw [ku.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr),
      ka.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)]
  · intro p hp
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · show u.mem.read (L.E + BitVec.ofNat 64 fScr) 8 = L.scr
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)), am,
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 fHdr) 8 = sigWord
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
        VG.Proof.Ed448.AArch64.Whole.read_writeW_self]
    · show u.mem.read (L.E + BitVec.ofNat 64 (fHdr + 8)) 8 = L.ctxLen <<< 8
      rw [um, VG.Proof.Ed448.AArch64.Whole.read_writeW_self]

end VG.Proof.Ed448.AArch64.Verify
