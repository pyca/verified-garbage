import VerifiedGarbage.Impl.Ed448.AArch64.Verify
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Entry
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap

/-!
# Ed448 verification on AArch64: where everything is

The contract the proof is written against (`vLocal`: the facts of
`Spec.Ed448.verifyContract` for 352 bytes of stack, stated for AArch64), and
the layout of a call (`Lay`): the buffers, the frame's base `E`, and the
`Env` of the frame's body, which keeps `scratch` and the header of `dom4` in
its locals.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Proof.Ed448.AArch64.Whole (Env WCtx sigWord TBL)
open VG.Impl.X448.AArch64.Base (combSym combWords)
open VG.Proof.X448.AArch64.Base (CombHeld)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

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
    s.rd = [pk, ctx, msg, sig, TBL (s.syms combSym)] ∧ s.wr = [scr] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 114 ≤ 2 ^ 64 ∧
      (s.gpr .x6).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧ CombHeld s [scr, stk]
  post s t := t.gpr .x0 = if Spec.Ed448.verify (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x5) 114) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.syms combSym = t.syms combSym

structure Lay where
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  sig : Addr
  scr : Addr
  E : Addr
  /-- The comb's tables (the static `combSym`), which `vg_ed448_verify_equation` reads. -/
  T : Addr

namespace Lay
variable (L : Lay)
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig, 114⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.E, 336⟩
abbrev TB : Region := TBL L.T

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
  tbfit : L.T.toNat + 8 * combWords.length ≤ 2 ^ 64

end Lay

theorem frame_sub (L : Lay) : Region.Sub (FR L.E) L.STK := Region.sub_prefix (by decide : 256 ≤ 336)

theorem env_ok {L : Lay} (hL : L.Ok) : L.env.Ok where
  args := by simp [Lay.env]
  ls := by simp [Lay.env, fScr, fHdr]
  fo := by
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.kc.sub_left (frame_sub L)
  co := by
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.ck
  e16 := hL.e16
  tin := by simp [Lay.env, Lay.inputs]
  tfr := hL.tbk.sub_right (frame_sub L)
  tck := hL.tbck
  tout := by
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.tbc
  tfit := hL.tbfit

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6,
    VG.Proof.Ed25519.AArch64.Whole.base s, s.syms combSym⟩

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
