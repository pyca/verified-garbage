module

public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Ed448.AArch64.Verify
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Entry
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Static
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! ### `Ed448.AArch64.Verify.Body`, which this module and modules that import it used -/

section

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
  exact hc.frame.readW (r := ARGS L.E) (Offset.contains _ (e := 256) (k := 48) (by omega_using []) (by omega_using [hj])
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
    have := List.mem_range.mp hi; omega_using [hn, this])
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
      Offset.contains _ (e := 256) (k := 48) (by omega_using []) (by omega_using []) (by decide)⟩)) fun u ⟨ku, um⟩ su => ?_
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

end

end

/-! ### `Ed448.AArch64.Verify.Calls`, which this module and modules that import it used -/

section

/-! The public verifier's call of the sparse equation, with its smaller static table. -/

@[expose] public section
namespace VG.Proof.Ed448.AArch64.Verify
open VG VG.AArch64
open VG.Proof.Ed448.AArch64.Whole
open VG.Impl.Ed448.AArch64.Sparse (baseSym baseWords)
open VG.Proof.Ed448.AArch64.Sparse (BaseHeld)
open VG.Proof.Ed25519.AArch64.Whole (FR CK Within)
variable {V:Env} {g:Reg → Addr} {vec:VReg → BitVec 128} {m₀:Mem} {u:State}

theorem baseHeld_of (hV : V.Ok) (hcfg:V.sym=baseSym ∧ V.words=baseWords) (hu : WCtx V g vec m₀ u) (hm : TblWords V.T m₀ baseWords) {ws : List Region}
    (hw : ∀ r ∈ ws, Writable V r) (rd wr : List Region) :
    BaseHeld (u.callEntry.withRegions rd wr) ws := by
  have hT : (u.callEntry.withRegions rd wr).syms baseSym = V.T := by rw [←hcfg.1];exact hu.2.2
  refine ⟨fun i hi => ?_, ?_, fun r hr => ?_⟩
  · rw [hT]; have hh:=hu.tbl hV (by rw [hcfg.2];exact hm)
    rw [hcfg.2] at hh
    exact hh i hi
  · rw [hT]; simpa only [hcfg.2] using hV.tfit
  · rw [hT]; simpa only [hcfg.2] using (hw r hr).tbl hV

theorem equation_pre {pk sig ch scr T : Addr} (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig)
    (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hs : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64) (hT : u.syms baseSym = T)
    (ht : BaseHeld (u.callEntry.withRegions [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩, TBL T baseWords] [⟨scr, 8192⟩])
      [⟨scr, 8192⟩]) :
    Proof.Ed448.AArch64.Sparse.verifyEquationLocal.pre
      (u.callEntry.withRegions [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩, TBL T baseWords] [⟨scr, 8192⟩]) := by
  have e3 := State.callEntry_gpr u (by decide : Reg.x3 ∉ linkRegs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3, syms_entry, hT]
  exacts [hp, hs, hc, hn, by rw [e3, h3] at *; exact ht]

theorem equation_call (hQ : Proof.Ed448.AArch64.Sparse.EqOk) (hV : V.Ok) (hcfg:V.sym=baseSym ∧ V.words=baseWords)
    (hu : WCtx V g vec m₀ u) {pk sig ch scr : Addr}
    (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig) (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hdp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hds : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hdc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64)
    (hrp : Readable V ⟨pk, 57⟩) (hrs : Readable V ⟨sig, 114⟩) (hrc : Readable V ⟨ch, 57⟩)
    (hws : Writable V ⟨scr, 8192⟩) (hm : TblWords V.T m₀ baseWords) :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.AArch64.Sparse.verifyEquation) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem pk 57)
        (Spec.Ed448.bytesAt u.mem sig 114) (Spec.Ed448.bytesAt u.mem ch 57) then 1 else 0 := by
  have hw : ∀ r ∈ [(⟨scr, 8192⟩ : Region)], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact hws
  have hrd : ∀ r ∈ [(⟨pk, 57⟩ : Region), ⟨sig, 114⟩, ⟨ch, 57⟩, TBL V.T baseWords], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exact hrp
    · exact hrs
    · exact hrc
    · simpa only [hcfg.2] using tbl_readable hV
  refine wcall hV hu (hQ.ok) (noFrames_depth Proof.Ed448.AArch64.Sparse.verifyEquation_noFrames)
    (equation_pre h0 h1 h2 h3 hdp hds hdc hn (by simpa only [hcfg.1] using hu.2.2) (baseHeld_of hV hcfg hu hm hw _ _))
    (covers_rw hrd hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x0) 57)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 114)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x2) 57) then 1 else 0 at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2] at hp
  exact hp

end VG.Proof.Ed448.AArch64.Verify

end

end

/-! ### `Ed448.AArch64.Verify.Hash`, which this module and modules that import it used -/

section

/-!
# Ed448 verification on AArch64: the hash

`H(dom4(0, C) ‖ R ‖ A ‖ M)` into the locals at `fH` (`hash_ok`): the state
zeroed, the header of `dom4` (kept in the locals), the context, `R`, the
public key and the message absorbed in turn, each from the position the
previous one returned, the padding, and 114 bytes squeezed.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue srcValid noRet ScrOk ST KS
  st_within ks_within kabs_chain kpad_ok ksqz_ok zeroSt_ok repr_nil hdr_bytes shake256_eq ofNat_toNat64
  readW_eq_read Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK ck_frame)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- What is hashed: `dom4(0, C) ‖ R ‖ A ‖ M`. -/
abbrev hashIn (L : Lay) (m : Mem) : List Byte :=
  hdrBytes L ++ Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ Spec.Sha3.bytesAt m L.sig 57 ++
    Spec.Sha3.bytesAt m L.pk 57 ++ Spec.Sha3.bytesAt m L.msg L.len.toNat

theorem scrOk (hL : L.Ok) : ScrOk L.env fScr L.scr := ⟨by simp [Lay.env], by simp [Lay.env], hL.nc⟩

/-- A region of the locals misses `scratch`. -/
theorem fr_st (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ (ST L.scr) :=
  (hL.kc.sub_left (Offset.sub_base _ h)).sub_right (st_within L.scr).sub
theorem fr_ks (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ (KS L.scr) :=
  (hL.kc.sub_left (Offset.sub_base _ h)).sub_right (ks_within L.scr).sub

theorem within_self (p : Addr) (n : Nat) : Within ⟨p, n⟩ ⟨p, n⟩ := ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem in_readable (R : Region) (hR : R ∈ L.inputs) :
    Within R (FR L.E) ∨ ∃ R' ∈ L.env.ins ++ L.env.outs, Within R R' :=
  .inr ⟨R, by simp [Lay.env, hR], within_self R.base R.len⟩

/-- The hash. -/
theorem hash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : Args L m₀) :
    WP isa (Impl.Ed448.AArch64.Verify.hash v.callee) t fun u => WCtx L.env g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 = Spec.Sha3.shake256 (hashIn L m₀) 114 := by
  have hV := env_ok hL
  have hs := scrOk hL
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, _, hz₁⟩ => ?_)
  -- The header.
  have k0 := hc₁.2.1 (fHdr, sigWord) (by simp [Lay.env])
  have k8 := hc₁.2.1 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  have hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
    (repr_nil hz₁)) fun t₂ ⟨hc₂, _, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  -- The context.
  have a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := arg_src hL hc₂.1 ha (j := 1) (by decide) _
  have a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (arg_src hL hc₂.1 ha (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs])) (hL.cc.sub_right (st_within L.scr).sub)
    (hL.cc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, _, hr₃, hx₃⟩ => ?_)
  have eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  -- `R`.
  have a5 : srcValue L.env.E t₃.mem (t₃.gpr .x0) aSig = L.sig := arg_src hL hc₃.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := aSig) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a5 rfl hx₃ (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide))) hr₃)
    fun t₄ ⟨hc₄, _, hr₄, hx₄⟩ => ?_)
  have eS : Spec.Sha3.bytesAt t₃.mem L.sig 57 = Spec.Sha3.bytesAt m₀ L.sig 57 :=
    in_bytes hL hc₃.1 (R := L.SIG) (by simp [Lay.inputs]) (show 57 ≤ 114 by decide) (show 114 ≤ 2 ^ 64 by decide)
  rw [eS] at hr₄ hx₄
  -- The public key.
  have a0 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aPk = L.pk := arg_src hL hc₄.1 ha (j := 0) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aPk) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a0 rfl hx₄ (by decide)
    (in_readable L.PK (by simp [Lay.inputs])) (hL.pc.sub_right (st_within L.scr).sub)
    (hL.pc.sub_right (ks_within L.scr).sub) hL.cp hr₄) fun t₅ ⟨hc₅, _, hr₅, hx₅⟩ => ?_)
  have eP : Spec.Sha3.bytesAt t₄.mem L.pk 57 = Spec.Sha3.bytesAt m₀ L.pk 57 :=
    in_bytes hL hc₄.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eP] at hr₅ hx₅
  -- The message.
  have a3 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aMsg = L.msg := arg_src hL hc₅.1 ha (j := 3) (by decide) _
  have a4 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aLen = BitVec.ofNat 64 L.len.toNat :=
    (arg_src hL hc₅.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₅ (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a3 a4
    hx₅ L.len.isLt (in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₅) fun t₆ ⟨hc₆, _, hr₆, hx₆⟩ => ?_)
  have eM : Spec.Sha3.bytesAt t₅.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    in_bytes hL hc₅.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₆ hx₆
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₆ (pos := .ret) trivial hx₆ (Nat.mod_lt _ (by decide)))
    fun t₇ ⟨hc₇, _, hp₇⟩ => ?_)
  have hst := hp₇ _ hr₆ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₇ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fScr, fHdr, fH]) (by simp [fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, _, hb⟩ => ⟨hu, ?_⟩
  rw [hb, hst, ← shake256_eq]

end VG.Proof.Ed448.AArch64.Verify

end

end

/-!
# Ed448 verification on AArch64: the frame's body

After the hash: `k`, the hash reduced modulo `L` (`reduce_step`), and the
verification equation's result in `x0` (`equation_step`), for the inputs as
on entry (`body_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call
  Readable Writable Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

attribute [local irreducible] VG.Impl.X448.AArch64.Base.combWords VG.Impl.Ed448.AArch64.Sparse.baseWords

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem scr_writable (L : Lay) : Writable L.env L.SCR := .inr ⟨L.SCR, by simp [Lay.env], within_self _ _⟩

theorem fr_scr (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.SCR :=
  hL.kc.sub_left (Offset.sub_base _ h)

theorem k_apart (L : Lay) : Apart L.env ⟨L.E + BitVec.ofNat 64 fK, 57⟩ :=
  ⟨⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩, fun p hp => by
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by simp [fScr, fHdr, fK]) (by simp [fScr, fHdr]) (by simp [fK])⟩

theorem reduce_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (callS reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fK) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceArgs) (by decide)
    (by simp [reduceArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fK, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.E + BitVec.ofNat 64 fK := hv (.x0, .val (.frame fK)) (List.mem_of_getElem? (i := 0) rfl)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (k_apart L)) (scr_writable L)) fun w ⟨hw, _, hk⟩ => ⟨hw, by rw [hk, hm]⟩

theorem equation_step (hQ : Proof.Ed448.AArch64.Sparse.EqOk) (hL : L.Ok)
    (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS equationArgs "vg_ed448_verify_equation" Impl.Ed448.AArch64.Sparse.verifyEquation) t fun u =>
      WCtx L.env g vec m₀ u ∧ u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57)
        (Spec.Ed448.bytesAt m₀ L.sig 114) (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fK) 57) then 1 else 0 := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := equationArgs) (by decide)
    (by simp [equationArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, aPk, aSig, fK, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.pk := (hv (.x0, aPk) (List.mem_of_getElem? (i := 0) rfl)).trans
    (arg_src hL hc.1 ha (j := 0) (by decide) _)
  have h1 : u.gpr .x1 = L.sig := (hv (.x1, aSig) (List.mem_of_getElem? (i := 1) rfl)).trans
    (arg_src hL hc.1 ha (j := 5) (by decide) _)
  have h2 : u.gpr .x2 = L.E + BitVec.ofNat 64 fK := hv (.x2, .val (.frame fK)) (List.mem_of_getElem? (i := 2) rfl)
  have h3 : u.gpr .x3 = L.scr := by
    rw [hv (.x3, .loc fScr 0) (List.mem_of_getElem? (i := 3) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (equation_call hQ hV ⟨rfl,rfl⟩ hu h0 h1 h2 h3 hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L) ha.2) fun w ⟨hw, _, hx⟩ => ⟨hw, ?_⟩
  have eP : Spec.Ed448.bytesAt u.mem L.pk 57 = Spec.Ed448.bytesAt m₀ L.pk 57 :=
    in_bytes hL hu.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  have eS : Spec.Ed448.bytesAt u.mem L.sig 114 = Spec.Ed448.bytesAt m₀ L.sig 114 :=
    in_bytes hL hu.1 (R := L.SIG) (by simp [Lay.inputs]) (Nat.le_refl _) (show 114 ≤ 2 ^ 64 by decide)
  rw [hx, eP, eS, hm]

/-- The frame's body: `x0` is the verification equation's result for the
reduced hash. -/
theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.Sparse.EqOk)
    (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.scr)
    (hsy : t.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T) :
    WP isa (body v.callee) t fun u => Ctx0 L g vec m₀ u ∧
      u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57) (Spec.Ed448.bytesAt m₀ L.sig 114)
        (Spec.Ed448.scalarReduce (Spec.Sha3.shake256 (hashIn L m₀) 114)) then 1 else 0 := by
  refine WP.seq (WP.mono (entry_ok hL hc ha h6 hsy) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (hash_ok v hL hc₁ ha) fun t₂ ⟨hc₂, hh₂⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step hL hc₂) fun t₃ ⟨hc₃, hk₃⟩ => ?_)
  refine WP.mono (equation_step hQ hL hc₃ ha) fun u ⟨hu, hx⟩ => ⟨hu.1, ?_⟩
  rw [hx, hk₃, show Spec.Ed448.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 =
    Spec.Sha3.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 from rfl, hh₂]

end VG.Proof.Ed448.AArch64.Verify
