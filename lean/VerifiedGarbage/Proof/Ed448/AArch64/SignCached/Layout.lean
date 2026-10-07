import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Entry
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap

/-!
# Ed448 signing with a cached public key on AArch64: where everything is

The contract the proof is written against (`scLocal`: the facts of
`Spec.Ed448.signCachedContract` for 352 bytes of stack, stated for AArch64),
and the layout of a call (`Lay`): the buffers, the frame's base `E`, and the
`Env` of the frame's body, which keeps `len`, `scratch` and the header of
`dom4` in its locals.
-/

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
