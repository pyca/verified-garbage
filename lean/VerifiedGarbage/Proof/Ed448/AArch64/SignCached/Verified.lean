import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Layout`. -/
section

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
open VG.Proof.Ed448.AArch64.Whole (Env sigWord)
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
    s.rd = [seed, pk, ctx, msg] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint ctx ∧ out.Disjoint msg ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧
      stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 114 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat ∧
      Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) ∧
      (s.gpr .x4).toNat ≤ 255
  post s t := Spec.Ed448.bytesAt t.mem (s.gpr .x0) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) (Spec.Ed448.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.gpr .x7 = t.gpr .x7

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

namespace Lay
variable (L : VG.Proof.Ed448.AArch64.SignCached.Lay)
abbrev OUT : Region := ⟨L.out, 114⟩
abbrev SEED : Region := ⟨L.seed, 57⟩
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.E, 336⟩

/-- The saved argument `j`. -/
def arg (j : Nat) : Addr :=
  match j with | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.ctx | 4 => L.ctxLen | _ => L.msg

def inputs : List Region := [L.SEED, L.PK, L.CTX, L.MSG]

/-- The frame's body: it reads the inputs and the saved arguments, writes
`out` and `scratch`, and keeps `len`, `scratch` and the header of `dom4` in
its locals. -/
def env : VG.Proof.Ed448.AArch64.Whole.Env where
  E := L.E
  ins := L.inputs ++ [ARGS L.E]
  outs := [L.OUT, L.SCR]
  ls := [(fLen, L.len), (fScr, L.scr), (fHdr, sigWord), (fHdr + 8, L.ctxLen <<< 8)]

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

end Lay

theorem frame_sub (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Region.Sub (FR L.E) L.STK := Region.sub_prefix (by decide : 256 ≤ 336)

theorem env_ok {L : VG.Proof.Ed448.AArch64.SignCached.Lay} (hL : L.Ok) : L.env.Ok where
  args := by simp [Lay.env]
  ls := by simp [Lay.env, fLen, fScr, fHdr]
  fo := by
    intro R hR
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hL.ko.sub_left (VG.Proof.Ed448.AArch64.SignCached.frame_sub L)
    · exact hL.kc.sub_left (VG.Proof.Ed448.AArch64.SignCached.frame_sub L)
  co := by
    intro R hR
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hL.co
    · exact hL.cc
  e16 := hL.e16

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Ed448.AArch64.SignCached.Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    VG.Proof.Ed25519.AArch64.Whole.base s⟩

theorem lay_ok {s : State} (h : scLocal.pre s) : (VG.Proof.Ed448.AArch64.SignCached.lay s).Ok := by
  obtain ⟨_, _, os, op, ox, om, oc, sc, pc, xc, mc, ko, ks, kp, kx, km, kc, no, ns, np, nc, hsp, _, hc⟩ := h
  have st := VG.Proof.Ed25519.AArch64.Whole.stk_sub s
  have ck := VG.Proof.Ed25519.AArch64.Whole.ck_sub s
  exact ⟨os, op, ox, om, oc, sc, pc, xc, mc, ko.sub_left st, ks.sub_left st, kp.sub_left st, kx.sub_left st,
    km.sub_left st, kc.sub_left st, ko.sub_left ck, ks.sub_left ck, kp.sub_left ck, kx.sub_left ck,
    km.sub_left ck, kc.sub_left ck, no, ns, np, nc, VG.Proof.Ed25519.AArch64.Whole.base_16 hsp,
    show (s.gpr .x4).toNat < 256 by omega⟩

end VG.Proof.Ed448.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Body`. -/
section

/-!
# Ed448 signing with a cached public key on AArch64: the frame's entry

The saved arguments (`Args`) as the body reads them (`arg_src`), the inputs'
bytes as on entry (`in_bytes`), and the entry, which keeps `len` and
`scratch` and writes the header of `dom4` in the locals (`entry_ok`).
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS keep hdr)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue readW_eq_read)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

variable {L : VG.Proof.Ed448.AArch64.SignCached.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The saved arguments. -/
def Args (L : VG.Proof.Ed448.AArch64.SignCached.Lay) (m : Mem) : Prop := ∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.arg j

abbrev Ctx0 (L : VG.Proof.Ed448.AArch64.SignCached.Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.env.ins L.env.outs t

theorem args_sub (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Region.Sub (ARGS L.E) L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- What the body may write misses the saved arguments. -/
theorem args_apart (hL : L.Ok) : ∀ r ∈ L.env.outs ++ [FR L.E, CK L.E], (ARGS L.E).Disjoint r := by
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.ko.sub_left (VG.Proof.Ed448.AArch64.SignCached.args_sub L)
  · exact hL.kc.sub_left (VG.Proof.Ed448.AArch64.SignCached.args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

theorem arg_word (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.SignCached.Ctx0 L g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) {j : Nat} (hj : j < 6) :
    t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * j)) 8 = L.arg j := by
  rw [← readW_eq_read, ← ha j hj]
  exact hc.frame.readW (r := ARGS L.E) (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega)
    (by decide)) (VG.Proof.Ed448.AArch64.SignCached.args_apart hL) (by decide)

theorem arg_src (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.SignCached.Ctx0 L g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) {j : Nat} (hj : j < 6)
    (x0 : BitVec 64) : srcValue L.E t.mem x0 (.val (.caller j 0)) = L.arg j := by
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value]
  rw [VG.Proof.Ed448.AArch64.SignCached.arg_word hL hc ha hj, BitVec.add_zero]

/-- An input's bytes, as on entry. -/
theorem in_bytes (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.SignCached.Ctx0 L g vec m₀ t) {R : Region} (hR : R ∈ L.inputs)
    {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt t.mem R.base n = Spec.Sha3.bytesAt m₀ R.base n := by
  unfold Spec.Sha3.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := R) ?_ hl (by
    have := List.mem_range.mp hi; omega)
  simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hR
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) <;> rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.os.symm, hL.op.symm, hL.ox.symm, hL.om.symm, hL.sc, hL.pc, hL.xc, hL.mc,
    (hL.ks.sub_left (VG.Proof.Ed448.AArch64.SignCached.frame_sub L)).symm, (hL.kp.sub_left (VG.Proof.Ed448.AArch64.SignCached.frame_sub L)).symm,
    (hL.kx.sub_left (VG.Proof.Ed448.AArch64.SignCached.frame_sub L)).symm, (hL.km.sub_left (VG.Proof.Ed448.AArch64.SignCached.frame_sub L)).symm, hL.cs.symm, hL.cp.symm,
    hL.cx.symm, hL.cm.symm]

/-- `len` and `scratch` kept, and the header of `dom4`. -/
theorem entry_ok (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.SignCached.Ctx0 L g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) (h6 : t.gpr .x6 = L.len)
    (h7 : t.gpr .x7 = L.scr) :
    WP isa (.block entry) t fun u => WCtx L.env g vec m₀ u := by
  have hfr : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x6) (d := fLen) (by decide)
    ⟨_, hfr, Offset.contains_base _ (by decide) (by decide)⟩) fun a ⟨ka, _, am⟩ => ?_
  have hfa : (⟨a.sp, 256⟩ : Region) ∈ a.wr := by rw [ka.sp, ka.wr]; exact hfr
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x7) (d := fScr) (by decide)
    ⟨_, hfa, Offset.contains_base _ (by decide) (by decide)⟩) fun b ⟨kb, _, bm⟩ => ?_
  have hfb : (⟨b.sp, 256⟩ : Region) ∈ b.wr := by rw [kb.sp, kb.wr]; exact hfa
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.hdr_ok (d := fHdr) (j := 4) (by decide) (by decide) hfb (by
    rw [kb.rd, kb.wr, ka.rd, ka.wr, kb.sp, ka.sp, hc.rd, hc.wr, hc.sp]
    exact ⟨ARGS L.E, List.mem_append_left _ (by simp [Lay.env]),
      Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)⟩)) fun u ⟨ku, um⟩ => ?_
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x15), h6, hc.sp] at am
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x7 ≠ .x15), ka.regs .x7 (by decide) (by decide), h7,
    ka.sp, hc.sp] at bm
  rw [kb.sp, ka.sp, hc.sp] at um
  have hread : b.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 4)) 8 = L.ctxLen := by
    rw [bm, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)),
      am, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))]
    exact VG.Proof.Ed448.AArch64.SignCached.arg_word hL hc ha (j := 4) (by decide)
  rw [hread] at um
  have hf : Frame [FR L.E] t.mem u.mem := by
    rw [um, bm, am]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_)
      |>.writeW (List.mem_singleton_self _) _ ?_) |>.writeW (List.mem_singleton_self _) _ ?_
    all_goals exact Offset.contains_base _ (by decide) (by decide)
  refine ⟨hc.of_frame (ku.rd.trans (kb.rd.trans ka.rd)) (ku.wr.trans (kb.wr.trans ka.wr))
    (ku.sp.trans (kb.sp.trans ka.sp)) (fun r hr _ => ?_)
    (fun r _ => by rw [ku.v, kb.v, ka.v]) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl fun _ h => h), ?_⟩
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Hash`. -/
section

/-!
# Ed448 signing with a cached public key on AArch64: the hashes

Each into the locals at `fH`: `SHAKE256(seed, 114)` (`seedHash_ok`),
`SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` with the prefix in the locals
(`nonceHash_ok`), and `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` with `R` in the
first half of `out` (`chalHash_ok`). The header of `dom4` is kept in the
locals; each absorption starts from the position the previous one returned.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue srcValid noRet ScrOk ST KS
  st_within ks_within kabs_chain kpad_ok ksqz_ok zeroSt_ok repr_nil hdr_bytes shake256_eq ofNat_toNat64
  srcValue_loc Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK ck_frame)

variable {L : VG.Proof.Ed448.AArch64.SignCached.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- What is hashed for `r` and for `k`: `dom4(0, C) ‖ X ‖ M`. -/
abbrev domIn (L : VG.Proof.Ed448.AArch64.SignCached.Lay) (m : Mem) (X : List Byte) : List Byte :=
  VG.Proof.Ed448.AArch64.SignCached.hdrBytes L ++ Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ X ++ Spec.Sha3.bytesAt m L.msg L.len.toNat

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
  .inr ⟨R, by simp [Lay.env, hR], VG.Proof.Ed448.AArch64.SignCached.within_self R.base R.len⟩

/-- Bytes apart from what a step writes are kept. -/
theorem keep_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' R.base n = Spec.Sha3.bytesAt m R.base n := by
  unfold Spec.Sha3.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hl (by have := List.mem_range.mp hi; omega)

/-- A region apart from the sponge's writes. -/
theorem sponge_apart {R : Region} (hS : R.Disjoint (ST L.scr)) (hK : R.Disjoint (KS L.scr))
    (hC : (CK L.E).Disjoint R) : ∀ r ∈ [ST L.scr, KS L.scr, CK L.E], R.Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [hS, hK, hC.symm]

theorem len_src (hc : WCtx L.env g vec m₀ t) :
    srcValue L.env.E t.mem (t.gpr .x0) aLen = BitVec.ofNat 64 L.len.toNat := by
  rw [aLen, srcValue_loc hc.2 (show (fLen, L.len) ∈ L.env.ls by simp [Lay.env]) 0, BitVec.add_zero]
  exact (ofNat_toNat64 L.len).symm

/-- `SHAKE256(seed, 114)`. -/
theorem seedHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) :
    WP isa (seedHash v.callee) t fun u => WCtx L.env g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, _, hz₁⟩ => ?_)
  have a1 : srcValue L.env.E t₁.mem (t₁.gpr .x0) aSeed = L.seed := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₁.1 ha (j := 1) (by decide) _
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := aSeed) (len := .val (.const 57))
    (pos := .val (.const 0)) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) (show 0 < 65536 by decide)
    rfl rfl a1 rfl rfl (by decide) (VG.Proof.Ed448.AArch64.SignCached.in_readable L.SEED (by simp [Lay.inputs]))
    (hL.sc.sub_right (st_within L.scr).sub) (hL.sc.sub_right (ks_within L.scr).sub) hL.cs (VG.Proof.Ed448.AArch64.Whole.repr_nil hz₁))
    fun t₂ ⟨hc₂, _, hr₂, hx₂⟩ => ?_)
  have eS : Spec.Sha3.bytesAt t₁.mem L.seed 57 = Spec.Sha3.bytesAt m₀ L.seed 57 :=
    VG.Proof.Ed448.AArch64.SignCached.in_bytes hL hc₁.1 (R := L.SEED) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eS, List.nil_append] at hr₂ hx₂
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₂ (pos := .ret) trivial hx₂ (Nat.mod_lt _ (by decide)))
    fun t₃ ⟨hc₃, _, hp₃⟩ => ?_)
  have hst := hp₃ _ hr₂ rfl
  refine WP.mono (ksqz_ok v hV hs hc₃ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fLen, fScr, fHdr, fH]) (by simp [fLen, fScr, fHdr]) (by simp [fH])⟩)
    (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, _, hb⟩ => ⟨hu, ?_⟩
  rw [hb, hst, ← VG.Proof.Ed448.AArch64.Whole.shake256_eq]

/-- What a hash into the locals writes: `scratch`, the 16 bytes below the
frame, and the hash. -/
abbrev HW (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : List Region := [L.SCR, CK L.E, ⟨L.E + BitVec.ofNat 64 fH, 114⟩]

theorem hw_sub {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, r ∈ [ST L.scr, KS L.scr, CK L.E, ⟨L.E + BitVec.ofNat 64 fH, 114⟩]) :
    Frame (VG.Proof.Ed448.AArch64.SignCached.HW L) m m' := by
  refine hf.sub fun r hr => ?_
  have h' := h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (st_within L.scr).sub⟩
  · exact ⟨L.SCR, by simp, (ks_within L.scr).sub⟩
  · exact ⟨CK L.E, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The hash of `dom4(0, C) ‖ X ‖ M` into the locals, for `X` the 57 bytes
`xs` at `xp` (`x`), which the sponge's writes miss. -/
theorem domHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) {x : Src} (hvx : srcValid x) (hrx : noRet x = true) {xp : Addr}
    (hxp : ∀ {u : State}, WCtx L.env g vec m₀ u → srcValue L.env.E u.mem (u.gpr .x0) x = xp)
    (hin : Within ⟨xp, 57⟩ (FR L.E) ∨ ∃ R ∈ L.env.ins ++ L.env.outs, Within ⟨xp, 57⟩ R)
    (dS : Region.Disjoint ⟨xp, 57⟩ (ST L.scr)) (dK : Region.Disjoint ⟨xp, 57⟩ (KS L.scr))
    (kD : (CK L.E).Disjoint ⟨xp, 57⟩) :
    WP isa (.seq (VG.Impl.Ed448.AArch64.Whole.zeroSt fScr) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr (.val (.frame fHdr)) (.val (.const 10)) (.val (.const 0))) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aCtx aCtxLen .ret) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr x (.val (.const 57)) .ret) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aMsg aLen .ret) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kpad v.callee fScr .ret)
        (VG.Impl.Ed448.AArch64.Whole.ksqz v.callee fScr (.val (.frame fH)))) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame (VG.Proof.Ed448.AArch64.SignCached.HW L) t.mem u.mem ∧
        Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 =
        Spec.Sha3.shake256 (VG.Proof.Ed448.AArch64.SignCached.domIn L m₀ (Spec.Sha3.bytesAt t.mem xp 57)) 114 := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have hx := VG.Proof.Ed448.AArch64.SignCached.sponge_apart dS dK kD
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, hf₁, hz₁⟩ => ?_)
  have eX₁ : Spec.Sha3.bytesAt t₁.mem xp 57 = Spec.Sha3.bytesAt t.mem xp 57 :=
    VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨xp, 57⟩) hf₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact dS)
      (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The header.
  have k0 := hc₁.2 (fHdr, sigWord) (by simp [Lay.env])
  have k8 := hc₁.2 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  have hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = VG.Proof.Ed448.AArch64.SignCached.hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide))
    (ck_frame (by decide)) (VG.Proof.Ed448.AArch64.Whole.repr_nil hz₁)) fun t₂ ⟨hc₂, hf₂, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  have eX₂ := VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨xp, 57⟩) hf₂ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The context.
  have a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₂.1 ha (j := 3) (by decide) _
  have a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₂.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (VG.Proof.Ed448.AArch64.SignCached.in_readable L.CTX (by simp [Lay.inputs])) (hL.xc.sub_right (st_within L.scr).sub)
    (hL.xc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, hf₃, hr₃, hx₃⟩ => ?_)
  have eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    VG.Proof.Ed448.AArch64.SignCached.in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  have eX₃ := VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨xp, 57⟩) hf₃ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- `X`.
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := x) (len := .val (.const 57)) (pos := .ret)
    hvx (show 57 < 65536 by decide) trivial hrx rfl (hxp hc₃) rfl hx₃ (by decide) hin dS dK kD hr₃)
    fun t₄ ⟨hc₄, hf₄, hr₄, hx₄⟩ => ?_)
  rw [eX₃, eX₂, eX₁] at hr₄ hx₄
  -- The message.
  have a3 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aMsg = L.msg := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₄.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ trivial rfl rfl a3 (VG.Proof.Ed448.AArch64.SignCached.len_src hc₄)
    hx₄ L.len.isLt (VG.Proof.Ed448.AArch64.SignCached.in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₄) fun t₅ ⟨hc₅, hf₅, hr₅, hx₅⟩ => ?_)
  have eM : Spec.Sha3.bytesAt t₄.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    VG.Proof.Ed448.AArch64.SignCached.in_bytes hL hc₄.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₅ hx₅
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₅ (pos := .ret) trivial hx₅ (Nat.mod_lt _ (by decide)))
    fun t₆ ⟨hc₆, hf₆, hp₆⟩ => ?_)
  have hst := hp₆ _ hr₅ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₆ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fLen, fScr, fHdr, fH]) (by simp [fLen, fScr, fHdr]) (by simp [fH])⟩)
    (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, hf₇, hb⟩ => ⟨hu, ?_, ?_⟩
  · have w₁ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₁ (by simp)
    have w₂ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₂ (by simp [Lay.env])
    have w₃ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₃ (by simp [Lay.env])
    have w₄ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₄ (by simp [Lay.env])
    have w₅ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₅ (by simp [Lay.env])
    have w₆ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₆ (by simp [Lay.env])
    have w₇ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₇ (by simp [Lay.env])
    exact (((((w₁.trans w₂).trans w₃).trans w₄).trans w₅).trans w₆).trans w₇
  · rw [hb, hst, ← VG.Proof.Ed448.AArch64.Whole.shake256_eq]

/-- The hash of `dom4(0, C) ‖ R ‖ A ‖ M` into the locals, `R` in the first
half of `out`. -/
theorem chalHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) :
    WP isa (chalHash v.callee) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame (VG.Proof.Ed448.AArch64.SignCached.HW L) t.mem u.mem ∧
        Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 =
        Spec.Sha3.shake256 (VG.Proof.Ed448.AArch64.SignCached.domIn L m₀ (Spec.Sha3.bytesAt t.mem L.out 57 ++
          Spec.Sha3.bytesAt m₀ L.pk 57)) 114 := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have dS : Region.Disjoint ⟨L.out, 57⟩ (ST L.scr) :=
    (hL.oc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide))
  have dK : Region.Disjoint ⟨L.out, 57⟩ (KS L.scr) :=
    (hL.oc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide))
  have kD : (CK L.E).Disjoint ⟨L.out, 57⟩ := hL.co.sub_right (Region.sub_prefix (by decide))
  have hx := VG.Proof.Ed448.AArch64.SignCached.sponge_apart dS dK kD
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, hf₁, hz₁⟩ => ?_)
  have eX₁ : Spec.Sha3.bytesAt t₁.mem L.out 57 = Spec.Sha3.bytesAt t.mem L.out 57 :=
    VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨L.out, 57⟩) hf₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact dS)
      (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The header.
  have k0 := hc₁.2 (fHdr, sigWord) (by simp [Lay.env])
  have k8 := hc₁.2 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  have hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = VG.Proof.Ed448.AArch64.SignCached.hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide))
    (ck_frame (by decide)) (VG.Proof.Ed448.AArch64.Whole.repr_nil hz₁)) fun t₂ ⟨hc₂, hf₂, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  have eX₂ := VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨L.out, 57⟩) hf₂ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The context.
  have a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₂.1 ha (j := 3) (by decide) _
  have a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₂.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (VG.Proof.Ed448.AArch64.SignCached.in_readable L.CTX (by simp [Lay.inputs])) (hL.xc.sub_right (st_within L.scr).sub)
    (hL.xc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, hf₃, hr₃, hx₃⟩ => ?_)
  have eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    VG.Proof.Ed448.AArch64.SignCached.in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  have eX₃ := VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨L.out, 57⟩) hf₃ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- `R`.
  have a0 : srcValue L.env.E t₃.mem (t₃.gpr .x0) aOut = L.out := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₃.1 ha (j := 0) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := aOut) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a0 rfl hx₃ (by decide)
    (.inr ⟨L.OUT, by simp [Lay.env], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩) dS dK kD hr₃)
    fun t₄ ⟨hc₄, hf₄, hr₄, hx₄⟩ => ?_)
  rw [eX₃, eX₂, eX₁] at hr₄ hx₄
  -- The public key.
  have a2 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aPk = L.pk := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₄.1 ha (j := 2) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aPk) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a2 rfl hx₄ (by decide)
    (VG.Proof.Ed448.AArch64.SignCached.in_readable L.PK (by simp [Lay.inputs])) (hL.pc.sub_right (st_within L.scr).sub)
    (hL.pc.sub_right (ks_within L.scr).sub) hL.cp hr₄) fun t₄' ⟨hc₄', hf₄', hr₄', hx₄'⟩ => ?_)
  have eP : Spec.Sha3.bytesAt t₄.mem L.pk 57 = Spec.Sha3.bytesAt m₀ L.pk 57 :=
    VG.Proof.Ed448.AArch64.SignCached.in_bytes hL hc₄.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eP] at hr₄' hx₄'
  -- The message.
  have a3 : srcValue L.env.E t₄'.mem (t₄'.gpr .x0) aMsg = L.msg := VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc₄'.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄' (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ trivial rfl rfl a3 (VG.Proof.Ed448.AArch64.SignCached.len_src hc₄')
    hx₄' L.len.isLt (VG.Proof.Ed448.AArch64.SignCached.in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₄') fun t₅ ⟨hc₅, hf₅, hr₅, hx₅⟩ => ?_)
  have eM : Spec.Sha3.bytesAt t₄'.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    VG.Proof.Ed448.AArch64.SignCached.in_bytes hL hc₄'.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₅ hx₅
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₅ (pos := .ret) trivial hx₅ (Nat.mod_lt _ (by decide)))
    fun t₆ ⟨hc₆, hf₆, hp₆⟩ => ?_)
  have hst := hp₆ _ hr₅ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₆ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fLen, fScr, fHdr, fH]) (by simp [fLen, fScr, fHdr]) (by simp [fH])⟩)
    (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, hf₇, hb⟩ => ⟨hu, ?_, ?_⟩
  · have w₁ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₁ (by simp)
    have w₂ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₂ (by simp [Lay.env])
    have w₃ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₃ (by simp [Lay.env])
    have w₄ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₄ (by simp [Lay.env])
    have w₄' := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₄' (by simp [Lay.env])
    have w₅ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₅ (by simp [Lay.env])
    have w₆ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₆ (by simp [Lay.env])
    have w₇ := VG.Proof.Ed448.AArch64.SignCached.hw_sub (L := L) hf₇ (by simp [Lay.env])
    exact ((((((w₁.trans w₂).trans w₃).trans w₄).trans w₄').trans w₅).trans w₆).trans w₇
  · rw [hb, hst, ← VG.Proof.Ed448.AArch64.Whole.shake256_eq, VG.Proof.Ed448.AArch64.SignCached.domIn, List.append_assoc _ (Spec.Sha3.bytesAt t.mem L.out 57)]

end VG.Proof.Ed448.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Correct`. -/
section

/-!
# Ed448 signing with a cached public key on AArch64: the frame's body

Pruning (`prune_step`), the calls of the Ed448 primitives (`reduceR_step`,
`base_step`, `reduceK_step`, `mulAdd_step`), each with what it writes, the
locals cleared (`wipe_step`), and the body (`body_ok`): the signature in
`out`, for the inputs as on entry (`Proof.Ed448.sign_pipeline`).
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call base_call
  mulAdd_call Readable Writable Apart kept_frame prune_run sha3_bytesAt_length)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : VG.Proof.Ed448.AArch64.SignCached.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem ed448_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ed448.bytesAt m p n = Spec.Sha3.bytesAt m p n := rfl

theorem scr_writable (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Writable L.env L.SCR := .inr ⟨L.SCR, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.within_self _ _⟩

theorem outR_within (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Within ⟨L.out, 57⟩ L.OUT := ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩
theorem outS_within (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Within ⟨L.out + BitVec.ofNat 64 57, 57⟩ L.OUT :=
  ⟨57, rfl, by show 57 + 57 ≤ 114; decide⟩

theorem outR_writable (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Writable L.env ⟨L.out, 57⟩ := .inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outR_within L⟩
theorem outS_writable (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Writable L.env ⟨L.out + BitVec.ofNat 64 57, 57⟩ :=
  .inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outS_within L⟩

theorem fr_scr (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.SCR :=
  hL.kc.sub_left (Offset.sub_base _ h)

theorem fr_out (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.OUT :=
  hL.ko.sub_left (Offset.sub_base _ h)

/-- A region of the locals apart from the kept words. -/
theorem fr_apart {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 200) : Apart L.env ⟨L.E + BitVec.ofNat 64 d, n⟩ :=
  ⟨⟨d, rfl, by show d + n ≤ 256; omega⟩, fun p hp => by
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by simp [fLen, fScr, fHdr]; omega) (by simp [fLen, fScr, fHdr]) (by omega)⟩

theorem out_sep (hL : L.Ok) : Region.Disjoint ⟨L.out, 57⟩ ⟨L.out + BitVec.ofNat 64 57, 57⟩ := by
  have h := Offset.disjoint (L.out) (d := 0) (n := 57) (e := 57) (k := 57) (by omega) (by omega)
    (by have := hL.no; omega)
  rwa [BitVec.add_zero] at h

/-- The word of `out` at 57. -/
theorem outS_src (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) (x0 : BitVec 64) :
    srcValue L.env.E t.mem x0 aR = L.out + BitVec.ofNat 64 57 := by
  show t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 0)) 8 + BitVec.ofNat 64 57 = _
  rw [VG.Proof.Ed448.AArch64.SignCached.arg_word hL hc.1 ha (j := 0) (by decide)]
  rfl

/-- `s`: the hash pruned. -/
theorem prune_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) {hb : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114 = hb) :
    WP isa (.block VG.Impl.Ed448.AArch64.SignCached.prune) t fun u => WCtx L.env g vec m₀ u ∧
      Frame [⟨L.E + BitVec.ofNat 64 fS, 64⟩] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fS) 57) = Spec.Ed448.prune hb := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.1.sp, hc.1.wr]; exact List.mem_cons_self
  have hh' : Spec.Sha3.bytesAt t.mem (t.sp + BitVec.ofNat 64 fH) 114 = hb := by rw [hc.1.sp]; exact hh
  refine WP.mono (prune_run (h := fH) (d := fS) hwrite (by decide) (by decide) (by decide) (by decide)
    (by decide) hh') fun u ⟨hu, hf, hp⟩ => ?_
  rw [hc.1.sp] at hf hp
  refine ⟨hc.of_frame hV hu.rd hu.wr hu.sp (fun r hr _ => ?_) (fun r _ => by rw [hu.v]) hf ?_, hf, hp⟩
  · apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (VG.Proof.Ed448.AArch64.SignCached.fr_apart (by decide) (by decide))

/-- `r`, into the second half of `out`. -/
theorem reduceR_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) :
    WP isa (callS reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧
      Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceRArgs) (by decide)
    (by simp [reduceRArgs, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x0, aR) (List.mem_of_getElem? (i := 0) rfl)).trans (VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc ha _)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (VG.Proof.Ed448.AArch64.SignCached.scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (VG.Proof.Ed448.AArch64.SignCached.outS_writable L) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `R = [r]B`, into the first half of `out`. -/
theorem base_step (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.out, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (L.out + BitVec.ofNat 64 57) 57) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := baseArgs) (by decide)
    (by simp [baseArgs, aOut, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out :=
    (hv (.x0, aOut) (List.mem_of_getElem? (i := 0) rfl)).trans (VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 ha (j := 0) (by decide) _)
  have h1 : u.gpr .x1 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x1, aR) (List.mem_of_getElem? (i := 1) rfl)).trans (VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc ha _)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (VG.Proof.Ed448.AArch64.SignCached.scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (base_call hb hV hu h0 h1 h2 (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub)
    (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub) hL.nc (.inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outS_within L⟩)
    (VG.Proof.Ed448.AArch64.SignCached.outR_writable L) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `k`, over the hash. -/
theorem reduceK_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (callS reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.E + BitVec.ofNat 64 fH, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceKArgs) (by decide)
    (by simp [reduceKArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.E + BitVec.ofNat 64 fH := hv (.x0, .val (.frame fH)) (List.mem_of_getElem? (i := 0) rfl)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (VG.Proof.Ed448.AArch64.SignCached.scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (VG.Proof.Ed448.AArch64.SignCached.fr_apart (by decide) (by decide))) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L)) fun w ⟨hw, hf, hk⟩ =>
      ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `S = (r + k s) mod L`, into the second half of `out`. -/
theorem mulAdd_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.SignCached.Args L m₀) :
    WP isa (callS mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem (L.out + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 57)
          (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fS) 57) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := mulAddArgs) (by decide)
    (by simp [mulAddArgs, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fS, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x0, aR) (List.mem_of_getElem? (i := 0) rfl)).trans (VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc ha _)
  have h1 : u.gpr .x1 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x1, aR) (List.mem_of_getElem? (i := 1) rfl)).trans (VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc ha _)
  have h2 : u.gpr .x2 = L.E + BitVec.ofNat 64 fH := hv (.x2, .val (.frame fH)) (List.mem_of_getElem? (i := 2) rfl)
  have h3 : u.gpr .x3 = L.E + BitVec.ofNat 64 fS := hv (.x3, .val (.frame fS)) (List.mem_of_getElem? (i := 3) rfl)
  have h4 : u.gpr .x4 = L.scr := by
    rw [hv (.x4, .loc fScr 0) (List.mem_of_getElem? (i := 4) rfl), (VG.Proof.Ed448.AArch64.SignCached.scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (mulAdd_call hV hu h0 h1 h2 h3 h4 (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub)
    (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (.inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outS_within L⟩)
    (.inl ⟨fH, rfl, show fH + 57 ≤ 256 by decide⟩) (.inl ⟨fS, rfl, show fS + 57 ≤ 256 by decide⟩)
    (VG.Proof.Ed448.AArch64.SignCached.outS_writable L) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- The hash, `k` and `s` cleared. -/
theorem wipe_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (.block wipe) t fun u => WCtx L.env g vec m₀ u ∧
      Frame [⟨L.E + BitVec.ofNat 64 16, 184⟩] t.mem u.mem := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.Ctx.zeroWords hc.1 (start := 2) (count := 23) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨⟨hu, kept_frame hV hc.2 (hf.mono fun r hr => List.mem_append_left _ hr) fun r hr => ?_⟩, hf⟩
  rw [List.mem_singleton.mp hr]
  exact .inl (VG.Proof.Ed448.AArch64.SignCached.fr_apart (by decide) (by decide))

/-- The specification's hash input. -/
theorem dom_eq (L : VG.Proof.Ed448.AArch64.SignCached.Lay) (m : Mem) (X : List Byte) :
    VG.Proof.Ed448.AArch64.SignCached.domIn L m X = Spec.Ed448.dom4 0 (Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat) ++
      (X ++ Spec.Sha3.bytesAt m L.msg L.len.toNat) := by
  simp only [VG.Proof.Ed448.AArch64.SignCached.domIn, VG.Proof.Ed448.AArch64.SignCached.hdrBytes, Spec.Ed448.dom4, sha3_bytesAt_length, List.append_assoc, List.cons_append,
    List.nil_append]

theorem bytes_split (m : Mem) (p : Addr) :
    Spec.Sha3.bytesAt m p 114 = Spec.Sha3.bytesAt m p 57 ++ Spec.Sha3.bytesAt m (p + BitVec.ofNat 64 57) 57 :=
  Proof.X25519.bytesAt_add m p 57 57

end VG.Proof.Ed448.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Run`. -/
section

/-!
# Ed448 signing with a cached public key on AArch64: the body's run

The body's steps in turn (`body_ok`), each keeping what later steps read
(`s`, `r` and `R`, apart from what each step writes), and the signature
`R ‖ S` in `out`: `Proof.Ed448.sign_pipeline`.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Proof.Ed448.AArch64.Whole (WCtx ST KS st_within ks_within sha3_bytesAt_length)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : VG.Proof.Ed448.AArch64.SignCached.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- 57 bytes apart from what a step writes are kept. -/
theorem keep57 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 57⟩ r) : Spec.Ed448.bytesAt m' p 57 = Spec.Ed448.bytesAt m p 57 :=
  VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨p, 57⟩) hf hd (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)

/-- `s`, `r` and `R` miss what the steps after they are written write. -/
structure Apart57 (L : VG.Proof.Ed448.AArch64.SignCached.Lay) (p : Addr) : Prop where
  scr : Region.Disjoint ⟨p, 57⟩ L.SCR
  ck : Region.Disjoint ⟨p, 57⟩ (CK L.E)
  h : Region.Disjoint ⟨p, 57⟩ ⟨L.E + BitVec.ofNat 64 fH, 114⟩
  k : Region.Disjoint ⟨p, 57⟩ ⟨L.E + BitVec.ofNat 64 fH, 57⟩

theorem Apart57.hw {p : Addr} (h : VG.Proof.Ed448.AArch64.SignCached.Apart57 L p) : ∀ r ∈ VG.Proof.Ed448.AArch64.SignCached.HW L, Region.Disjoint ⟨p, 57⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [h.scr, h.ck, h.h]

theorem Apart57.call {p q : Addr} (h : VG.Proof.Ed448.AArch64.SignCached.Apart57 L p) (hq : Region.Disjoint ⟨p, 57⟩ ⟨q, 57⟩) :
    ∀ r ∈ [⟨q, 57⟩, L.SCR, CK L.E], Region.Disjoint ⟨p, 57⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [hq, h.scr, h.ck]

theorem apart_out (hL : L.Ok) : VG.Proof.Ed448.AArch64.SignCached.Apart57 L L.out where
  scr := hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub
  ck := (hL.co.sub_right (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub).symm
  h := (VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).symm.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub
  k := (VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).symm.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub

theorem apart_outS (hL : L.Ok) : VG.Proof.Ed448.AArch64.SignCached.Apart57 L (L.out + BitVec.ofNat 64 57) where
  scr := hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub
  ck := (hL.co.sub_right (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub).symm
  h := (VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).symm.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub
  k := (VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).symm.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub

theorem apart_s (hL : L.Ok) : VG.Proof.Ed448.AArch64.SignCached.Apart57 L (L.E + BitVec.ofNat 64 fS) where
  scr := VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)
  ck := (ck_frame (by decide)).symm
  h := Offset.disjoint _ (by decide) (by decide) (by decide)
  k := Offset.disjoint _ (by decide) (by decide) (by decide)

/-- `H(dom4(0, C) ‖ X ‖ M)` as the specification writes it. -/
theorem hash_eq (L : VG.Proof.Ed448.AArch64.SignCached.Lay) (m : Mem) (X : List Byte) :
    Spec.Sha3.shake256 (VG.Proof.Ed448.AArch64.SignCached.domIn L m X) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m L.ctx L.ctxLen.toNat) (X ++ Spec.Ed448.bytesAt m L.msg L.len.toNat) := by
  rw [VG.Proof.Ed448.AArch64.SignCached.dom_eq]
  rfl

theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.len) (h7 : t.gpr .x7 = L.scr)
    (hpk : Spec.Ed448.bytesAt m₀ L.pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57)) :
    WP isa (VG.Impl.Ed448.AArch64.SignCached.body v.callee) t fun u => VG.Proof.Ed448.AArch64.SignCached.Ctx0 L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 114 = Spec.Ed448.sign (Spec.Ed448.bytesAt m₀ L.seed 57)
        (Spec.Ed448.bytesAt m₀ L.ctx L.ctxLen.toNat) (Spec.Ed448.bytesAt m₀ L.msg L.len.toNat) := by
  have aR := VG.Proof.Ed448.AArch64.SignCached.apart_out hL
  have ar := VG.Proof.Ed448.AArch64.SignCached.apart_outS hL
  have as := VG.Proof.Ed448.AArch64.SignCached.apart_s hL
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.entry_ok hL hc ha h6 h7) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.seedHash_ok v hL hc₁ ha) fun t₂ ⟨hc₂, hH₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.prune_step hL hc₂ hH₂) fun t₃ ⟨hc₃, hf₃, hs₃⟩ => ?_)
  have hp₃ : Spec.Sha3.bytesAt t₃.mem (L.E + BitVec.ofNat 64 (fH + 57)) 57 =
      (Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114).drop 57 := by
    rw [VG.Proof.Ed448.AArch64.SignCached.keep_bytes (R := ⟨L.E + BitVec.ofNat 64 (fH + 57), 57⟩) hf₃ (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide), ← hH₂, VG.Proof.Ed448.AArch64.SignCached.bytes_split, Offset.add_add,
      List.drop_left' (sha3_bytesAt_length _ _ _)]
  -- `r`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.domHash_ok v hL hc₃ ha (x := .val (.frame (fH + 57)))
    (show fH + 57 < 4096 by decide) rfl (xp := L.E + BitVec.ofNat 64 (fH + 57)) (fun _ => rfl)
    (.inl ⟨fH + 57, rfl, show fH + 57 + 57 ≤ 256 by decide⟩) (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide))
    (ck_frame (by decide))) fun t₄ ⟨hc₄, hf₄, hH₄⟩ => ?_)
  rw [hp₃] at hH₄
  have hs₄ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₄ as.hw
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.reduceR_step hL hc₄ ha) fun t₅ ⟨hc₅, hf₅, hr₅⟩ => ?_)
  have hs₅ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₅ (as.call ((VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).sub_right (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub))
  -- `R`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.base_step hb hL hc₅ ha) fun t₆ ⟨hc₆, hf₆, hR₆⟩ => ?_)
  have hs₆ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₆ (as.call ((VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).sub_right (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub))
  have hr₆ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₆ (ar.call (VG.Proof.Ed448.AArch64.SignCached.out_sep hL).symm)
  -- `k`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.chalHash_ok v hL hc₆ ha) fun t₇ ⟨hc₇, hf₇, hH₇⟩ => ?_)
  have hs₇ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₇ as.hw
  have hr₇ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₇ ar.hw
  have hR₇ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₇ aR.hw
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.reduceK_step hL hc₇) fun t₈ ⟨hc₈, hf₈, hk₈⟩ => ?_)
  have hs₈ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₈ (as.call as.k)
  have hr₈ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₈ (ar.call ar.k)
  have hR₈ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₈ (aR.call aR.k)
  -- `S`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.SignCached.mulAdd_step hL hc₈ ha) fun t₉ ⟨hc₉, hf₉, hS₉⟩ => ?_)
  have hR₉ := VG.Proof.Ed448.AArch64.SignCached.keep57 hf₉ (aR.call (VG.Proof.Ed448.AArch64.SignCached.out_sep hL))
  refine WP.mono (VG.Proof.Ed448.AArch64.SignCached.wipe_step hL hc₉) fun u ⟨hu, hf⟩ => ⟨hu.1, ?_⟩
  have hRu := VG.Proof.Ed448.AArch64.SignCached.keep57 hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).symm.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub
  have hSu := VG.Proof.Ed448.AArch64.SignCached.keep57 hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (VG.Proof.Ed448.AArch64.SignCached.fr_out hL (by decide)).symm.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub
  rw [VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt, VG.Proof.Ed448.AArch64.SignCached.bytes_split, ← VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt, ← VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt, hRu, hSu, hS₉, hR₉, hR₈, hR₇, hR₆,
    hr₈, hr₇, hr₆, hk₈, hs₈, hs₇, hs₆, hs₅, hs₄, hr₅, VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt _ _ 114, hH₄, VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt _ _ 114, hH₇,
    VG.Proof.Ed448.AArch64.SignCached.hash_eq, VG.Proof.Ed448.AArch64.SignCached.hash_eq, ← VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt, ← VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt _ L.out, hR₆, hr₅, VG.Proof.Ed448.AArch64.SignCached.ed448_bytesAt _ _ 114, hH₄, VG.Proof.Ed448.AArch64.SignCached.hash_eq]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs₃

end VG.Proof.Ed448.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Main`. -/
section

/-!
# Ed448 signing with a cached public key on AArch64: the whole function

`vg_ed448_sign_cached` meets `scLocal` and the ABI (`signCached_ok`), for any
implementation `v` of the Keccak permutation, given that
`vg_ed448_scalar_base` meets its contract (`BaseOk`): the frame
(`Proof.Ed25519.AArch64.Whole.wrap_ok`) runs the body, whose signature is
RFC 8032's for the inputs as on entry.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Proof.Ed25519.AArch64.Whole (entered bodyRd bodyWr)

theorem entry_writes {s : State} (h : scLocal.pre s) : ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem entry_below {s : State} (h : scLocal.pre s) : 352 ≤ s.sp.toNat :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : scLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    VG.Proof.Ed448.AArch64.SignCached.Ctx0 (VG.Proof.Ed448.AArch64.SignCached.lay s) s.gpr s.v p.mem (p.withRegions (bodyRd s) (bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [bodyRd, bodyWr, h.1, h.2.1, VG.Proof.Ed448.AArch64.SignCached.Ctx0, Lay.env, Lay.inputs, Lay.OUT, Lay.SEED, Lay.PK, Lay.CTX,
    Lay.MSG, Lay.SCR, VG.Proof.Ed448.AArch64.SignCached.lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    VG.Proof.Ed448.AArch64.SignCached.Args (VG.Proof.Ed448.AArch64.SignCached.lay s) p.mem := fun j hj => by
  have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_x6 {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).gpr .x6 = (VG.Proof.Ed448.AArch64.SignCached.lay s).len :=
  hp.step.regs .x6 (by decide)

theorem entry_x7 {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).gpr .x7 = (VG.Proof.Ed448.AArch64.SignCached.lay s).scr :=
  hp.step.regs .x7 (by decide)

theorem body_ctx {s p u : State} (h : scLocal.pre s) (hu : VG.Proof.Ed448.AArch64.SignCached.Ctx0 (VG.Proof.Ed448.AArch64.SignCached.lay s) s.gpr s.v p.mem u) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx (VG.Proof.Ed25519.AArch64.Whole.base s) s.gpr s.v p.mem (bodyRd s)
      s.wr u := by
  simpa only [bodyRd, bodyWr, h.1, h.2.1, VG.Proof.Ed448.AArch64.SignCached.Ctx0, Lay.env, Lay.inputs, Lay.OUT, Lay.SEED, Lay.PK, Lay.CTX,
    Lay.MSG, Lay.SCR, VG.Proof.Ed448.AArch64.SignCached.lay, List.cons_append, List.nil_append] using hu

/-- An input's bytes after the frame's writes, as on entry. -/
theorem below_bytes {m m' : Mem} {s : State} (hf : Frame [below s.sp 336] m m') {R : Region}
    (hd : (below s.sp 352).Disjoint R) {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' R.base n = Spec.Ed448.bytesAt m R.base n :=
  VG.Proof.Ed448.AArch64.SignCached.keep_bytes hf (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact (hd.sub_left (VG.Proof.Ed25519.AArch64.Whole.stk_sub s)).symm) hn hl

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (VG.Impl.Ed448.AArch64.SignCached.body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hr := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.reduce_noFrames
  have hb := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.base_noFrames
  have hm := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.mulAdd_noFrames
  simp only [VG.Impl.Ed448.AArch64.SignCached.body, seedHash, nonceHash, chalHash, Impl.Ed448.AArch64.Whole.zeroSt,
    Impl.Ed448.AArch64.Whole.kabs, Impl.Ed448.AArch64.Whole.kpad, Impl.Ed448.AArch64.Whole.ksqz,
    Impl.Ed448.AArch64.Whole.callS, Code.aarch64Depth, Nat.max_le, ha, hp, hs, hr, hb, hm]
  omega

theorem entry_pk {s p : State} (h : scLocal.pre s)
    (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    Spec.Ed448.bytesAt p.mem (VG.Proof.Ed448.AArch64.SignCached.lay s).pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (VG.Proof.Ed448.AArch64.SignCached.lay s).seed 57) := by
  have hf := VG.Proof.Ed25519.AArch64.Whole.saved_frame hp
  show Spec.Ed448.bytesAt p.mem (s.gpr .x2) 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (s.gpr .x1) 57)
  rw [VG.Proof.Ed448.AArch64.SignCached.below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x2, 57⟩) (n := 57) (Nat.le_refl _)
      (show 57 ≤ 2 ^ 64 by decide),
    VG.Proof.Ed448.AArch64.SignCached.below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x1, 57⟩) (n := 57) (Nat.le_refl _)
      (show 57 ≤ 2 ^ 64 by decide)]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The frame's body, from the state the frame enters it in. -/
theorem signCached_ok_body (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s p : State}
    (h : scLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    WP isa (VG.Impl.Ed448.AArch64.SignCached.body v.callee) (p.withRegions (bodyRd s) (bodyWr s)) fun u => VG.Proof.Ed448.AArch64.SignCached.Ctx0 (VG.Proof.Ed448.AArch64.SignCached.lay s) s.gpr s.v p.mem u ∧
      Spec.Ed448.bytesAt u.mem (VG.Proof.Ed448.AArch64.SignCached.lay s).out 114 = Spec.Ed448.sign (Spec.Ed448.bytesAt p.mem (VG.Proof.Ed448.AArch64.SignCached.lay s).seed 57)
        (Spec.Ed448.bytesAt p.mem (VG.Proof.Ed448.AArch64.SignCached.lay s).ctx (VG.Proof.Ed448.AArch64.SignCached.lay s).ctxLen.toNat)
        (Spec.Ed448.bytesAt p.mem (VG.Proof.Ed448.AArch64.SignCached.lay s).msg (VG.Proof.Ed448.AArch64.SignCached.lay s).len.toNat) :=
  VG.Proof.Ed448.AArch64.SignCached.body_ok v hb (VG.Proof.Ed448.AArch64.SignCached.lay_ok h) (VG.Proof.Ed448.AArch64.SignCached.entry_ctx h hp) (VG.Proof.Ed448.AArch64.SignCached.entry_args hp) (VG.Proof.Ed448.AArch64.SignCached.entry_x6 hp) (VG.Proof.Ed448.AArch64.SignCached.entry_x7 hp) (VG.Proof.Ed448.AArch64.SignCached.entry_pk h hp)

theorem signCached_ok (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) {s : State}
    (h : scLocal.pre s) :
    WP isa (signCachedWith v.callee) s fun u => abiPreserved s u ∧ scLocal.post s u := by
  have hw := VG.Proof.Ed25519.AArch64.Whole.wrap_ok (VG.Proof.Ed448.AArch64.SignCached.body_depth v) (VG.Proof.Ed448.AArch64.SignCached.entry_below h) (VG.Proof.Ed448.AArch64.SignCached.entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (s.gpr .x0) 114 = Spec.Ed448.sign
      (Spec.Ed448.bytesAt m (s.gpr .x1) 57) (Spec.Ed448.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Ed448.bytesAt m (s.gpr .x5) (s.gpr .x6).toNat))
    (fun p hp => WP.mono (VG.Proof.Ed448.AArch64.SignCached.signCached_ok_body v hb h hp) fun u ⟨hu, ho⟩ => ⟨VG.Proof.Ed448.AArch64.SignCached.body_ctx h hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  change Spec.Ed448.bytesAt u.mem (s.gpr .x0) 114 = _
  rw [hp, VG.Proof.Ed448.AArch64.SignCached.below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x1, 57⟩) (n := 57) (Nat.le_refl _)
      (show 57 ≤ 2 ^ 64 by decide),
    VG.Proof.Ed448.AArch64.SignCached.below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (n := (s.gpr .x4).toNat)
      (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _)),
    VG.Proof.Ed448.AArch64.SignCached.below_bytes hf h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (R := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩) (n := (s.gpr .x6).toNat)
      (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _))]

end VG.Proof.Ed448.AArch64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Verified`. -/
section

/-!
# Ed448 signing with a cached public key on AArch64: `Verified`

Correctness including the ABI (`signCached_ok`), for any implementation `v`
of the Keccak permutation, given that `vg_ed448_scalar_base` meets
its contract in constant time (`BaseOk`, which the generic file passes in). Constant time in every buffer's contents: two runs whose
pointers and lengths agree have the same layout, so in the frame's body they
are related by `Whole.Two`. The blocks address only the stack and
`scratch`, from registers that agree (the taint analysis); each call is of
constant-time code (the sponge functions for `v`, `vg_ed448_scalar_reduce`,
`vg_ed448_scalar_base`, `vg_ed448_scalar_mul_add`) whose public data, its
pointers, lengths and the sponge's positions, agree.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Two WCtx srcValue zeroSt_ct kabs_ct kpad_ct ksqz_ct reduce_ct base_ct
  mulAdd_ct block_ct ofNat_toNat64 st_within ks_within)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : VG.Proof.Ed448.AArch64.SignCached.Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

/-- The positions of the sponge after each absorption. -/
abbrev q1 : Nat := (0 + 10) % 136
abbrev q2 (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Nat := (VG.Proof.Ed448.AArch64.SignCached.q1 + L.ctxLen.toNat) % 136
abbrev q3 (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Nat := (VG.Proof.Ed448.AArch64.SignCached.q2 L + 57) % 136
abbrev q4 (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Nat := (VG.Proof.Ed448.AArch64.SignCached.q3 L + 57) % 136

theorem sqz_apart (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : VG.Proof.Ed448.AArch64.Whole.Apart L.env ⟨L.E + BitVec.ofNat 64 fH, 114⟩ :=
  VG.Proof.Ed448.AArch64.SignCached.fr_apart (by decide) (by decide)

theorem seedHash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : VG.Proof.Ed448.AArch64.SignCached.Args L m₁) (ha₂ : VG.Proof.Ed448.AArch64.SignCached.Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (seedHash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have z := zeroSt_ct hV hs ha₁ ha₂ (P := fun _ => True) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (by taint_decide)
  have k := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aSeed)
    (len := .val (.const 57)) (pos := .val (.const 0)) ⟨by decide, by decide⟩ (show 57 < 65536 by decide)
    (show 0 < 65536 by decide) rfl rfl (by taint_decide) (P := fun _ => True) (dp := L.seed) (n := 57) (q := 0)
    (fun hm hc _ => VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 1) (by decide) _) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (by decide) (by decide) (VG.Proof.Ed448.AArch64.SignCached.in_readable L.SEED (by simp [Lay.inputs]))
    (hL.sc.sub_right (st_within L.scr).sub) (hL.sc.sub_right (ks_within L.scr).sub) hL.cs
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := (0 + 57) % 136) (fun _ _ hp => hp) (by decide)
  have q := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl) (.inl (VG.Proof.Ed448.AArch64.SignCached.sqz_apart L)) (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide)) (ck_frame (by decide))
  exact z.seq (k.seq (p.seq q))

/-- The state zeroed, then `dom4(0, C)`: the header and the context, then `rest`. -/
theorem dom_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : VG.Proof.Ed448.AArch64.SignCached.Args L m₁) (ha₂ : VG.Proof.Ed448.AArch64.SignCached.Args L m₂)
    {rest : Prog isa}
    (hr : RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 (VG.Proof.Ed448.AArch64.SignCached.q2 L)) rest
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (.seq (VG.Impl.Ed448.AArch64.Whole.zeroSt fScr) <|
        .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr (.val (.frame fHdr)) (.val (.const 10))
          (.val (.const 0))) <|
        .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aCtx aCtxLen .ret) rest)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have z := zeroSt_ct hV hs ha₁ ha₂ (P := fun _ => True) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (by taint_decide)
  have k1 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := .val (.frame fHdr))
    (len := .val (.const 10)) (pos := .val (.const 0)) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl (by taint_decide) (P := fun _ => True)
    (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (q := 0) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (by decide) (by decide) (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩)
    (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide)) (ck_frame (by decide))
  have k2 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aCtx)
    (len := aCtxLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.ctx) (n := L.ctxLen.toNat) (q := VG.Proof.Ed448.AArch64.SignCached.q1)
    (fun hm hc _ => VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 3) (by decide) _)
    (fun hm hc _ => (VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 4) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm)
    (fun _ _ hp => hp) (by decide) L.ctxLen.isLt (VG.Proof.Ed448.AArch64.SignCached.in_readable L.CTX (by simp [Lay.inputs]))
    (hL.xc.sub_right (st_within L.scr).sub) (hL.xc.sub_right (ks_within L.scr).sub) hL.cx
  exact z.seq (k1.seq (k2.seq hr))

/-- The message, the padding and the output, from the position `q`. -/
theorem tail_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : VG.Proof.Ed448.AArch64.SignCached.Args L m₁) (ha₂ : VG.Proof.Ed448.AArch64.SignCached.Args L m₂)
    {q : Nat} (hq : q < 136) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 q)
      (.seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aMsg aLen .ret) <|
        .seq (VG.Impl.Ed448.AArch64.Whole.kpad v.callee fScr .ret)
          (VG.Impl.Ed448.AArch64.Whole.ksqz v.callee fScr (.val (.frame fH))))
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have k := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aMsg)
    (len := aLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.msg) (n := L.len.toNat) (q := q)
    (fun hm hc _ => VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 5) (by decide) _) (fun _ hc _ => VG.Proof.Ed448.AArch64.SignCached.len_src hc)
    (fun _ _ hp => hp) hq L.len.isLt (VG.Proof.Ed448.AArch64.SignCached.in_readable L.MSG (by simp [Lay.inputs]))
    (hL.mc.sub_right (st_within L.scr).sub) (hL.mc.sub_right (ks_within L.scr).sub) hL.cm
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := (q + L.len.toNat) % 136) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide))
  have o := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl) (.inl (VG.Proof.Ed448.AArch64.SignCached.sqz_apart L)) (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide)) (ck_frame (by decide))
  exact k.seq (p.seq o)

theorem nonceHash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : VG.Proof.Ed448.AArch64.SignCached.Args L m₁) (ha₂ : VG.Proof.Ed448.AArch64.SignCached.Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (nonceHash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have x := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := .val (.frame (fH + 57)))
    (len := .val (.const 57)) (pos := .ret) (show fH + 57 < 4096 by decide) (show 57 < 65536 by decide) trivial
    rfl rfl (by taint_decide) (dp := L.E + BitVec.ofNat 64 (fH + 57)) (n := 57) (q := VG.Proof.Ed448.AArch64.SignCached.q2 L)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide)
    (.inl ⟨fH + 57, rfl, show fH + 57 + 57 ≤ 256 by decide⟩) (VG.Proof.Ed448.AArch64.SignCached.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_ks hL (by decide))
    (ck_frame (by decide))
  have t := VG.Proof.Ed448.AArch64.SignCached.tail_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) v hL ha₁ ha₂ (q := VG.Proof.Ed448.AArch64.SignCached.q3 L) (Nat.mod_lt _ (by decide))
  exact VG.Proof.Ed448.AArch64.SignCached.dom_ct v hL ha₁ ha₂ (x.seq t)

theorem chalHash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : VG.Proof.Ed448.AArch64.SignCached.Args L m₁) (ha₂ : VG.Proof.Ed448.AArch64.SignCached.Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (chalHash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := VG.Proof.Ed448.AArch64.SignCached.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.SignCached.scrOk hL
  have r := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aOut)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.out) (n := 57) (q := VG.Proof.Ed448.AArch64.SignCached.q2 L)
    (fun hm hc _ => VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 0) (by decide) _) (fun _ _ _ => rfl) (fun _ _ hp => hp)
    (Nat.mod_lt _ (by decide)) (by decide) (.inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outR_within L⟩)
    (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub |>.sub_right (st_within L.scr).sub)
    (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub |>.sub_right (ks_within L.scr).sub)
    (hL.co.sub_right (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub)
  have k := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aPk)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.pk) (n := 57) (q := VG.Proof.Ed448.AArch64.SignCached.q3 L)
    (fun hm hc _ => VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 2) (by decide) _) (fun _ _ _ => rfl) (fun _ _ hp => hp)
    (Nat.mod_lt _ (by decide)) (by decide) (VG.Proof.Ed448.AArch64.SignCached.in_readable L.PK (by simp [Lay.inputs]))
    (hL.pc.sub_right (st_within L.scr).sub) (hL.pc.sub_right (ks_within L.scr).sub) hL.cp
  have t := VG.Proof.Ed448.AArch64.SignCached.tail_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) v hL ha₁ ha₂ (q := VG.Proof.Ed448.AArch64.SignCached.q4 L) (Nat.mod_lt _ (by decide))
  exact VG.Proof.Ed448.AArch64.SignCached.dom_ct v hL ha₁ ha₂ (r.seq (k.seq t))

/-- The arguments of the calls. -/
def reduceRVal (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Reg → Addr
  | .x0 => L.out + BitVec.ofNat 64 57
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

def baseVal (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Reg → Addr
  | .x0 => L.out
  | .x1 => L.out + BitVec.ofNat 64 57
  | _ => L.scr

def reduceKVal (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Reg → Addr
  | .x0 => L.E + BitVec.ofNat 64 fH
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

def mulAddVal (L : VG.Proof.Ed448.AArch64.SignCached.Lay) : Reg → Addr
  | .x0 => L.out + BitVec.ofNat 64 57
  | .x1 => L.out + BitVec.ofNat 64 57
  | .x2 => L.E + BitVec.ofNat 64 fH
  | .x3 => L.E + BitVec.ofNat 64 fS
  | _ => L.scr

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.len ∧ a.gpr .x7 = L.scr) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.len ∧ b.gpr .x7 = L.scr)) (body v.callee) fun _ _ => True := by
  have hV := env_ok hL
  have hs := scrOk hL
  have e : RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.len ∧ a.gpr .x7 = L.scr) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.len ∧ b.gpr .x7 = L.scr))
      (.block entry) (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
    VG.Proof.Ed25519.AArch64.Whole.rel_wp
      (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide))
      (fun _ h => WP.mono (VG.Proof.Ed448.AArch64.SignCached.entry_ok hL h.1 ha₁ h.2.1 h.2.2) fun _ hu => ⟨hu, trivial⟩)
      (fun _ h => WP.mono (VG.Proof.Ed448.AArch64.SignCached.entry_ok hL h.1 ha₂ h.2.1 h.2.2) fun _ hu => ⟨hu, trivial⟩)
  have pr := block_ct (V := L.env) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) ha₁ ha₂
    (P := fun _ => True) (Q := fun _ => True) (is := VG.Impl.Ed448.AArch64.SignCached.prune) (by taint_decide)
    fun _ hc _ => WP.mono (VG.Proof.Ed448.AArch64.SignCached.prune_step hL hc (hb := Spec.Sha3.bytesAt _ (L.E + BitVec.ofNat 64 fH) 114) rfl)
      fun _ hu => ⟨hu.1, trivial⟩
  have rr := reduce_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceRArgs)
    (by decide) (by simp [reduceRArgs, aR, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (VG.Proof.Ed448.AArch64.SignCached.reduceRVal L)
    (fun hm hc _ p hp => by
      simp only [reduceRArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc hm _
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (VG.Proof.Ed448.AArch64.SignCached.outS_writable L) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (VG.Proof.Ed448.AArch64.SignCached.reduceR_step hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  have bs := base_ct hb hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := baseArgs)
    (by decide) (by simp [baseArgs, aOut, aR, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (VG.Proof.Ed448.AArch64.SignCached.baseVal L)
    (fun hm hc _ p hp => by
      simp only [baseArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact VG.Proof.Ed448.AArch64.SignCached.arg_src hL hc.1 hm (j := 0) (by decide) _
      · exact VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc hm _
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outR_within L).sub) (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub) hL.nc
    (.inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outS_within L⟩) (VG.Proof.Ed448.AArch64.SignCached.outR_writable L) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (VG.Proof.Ed448.AArch64.SignCached.base_step hb hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  have rk := reduce_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceKArgs)
    (by decide) (by simp [reduceKArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (VG.Proof.Ed448.AArch64.SignCached.reduceKVal L)
    (fun _ hc _ p hp => by
      simp only [reduceKArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (VG.Proof.Ed448.AArch64.SignCached.fr_apart (by decide) (by decide))) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L) (Q := fun _ => True)
    (fun _ hc _ => WP.mono (VG.Proof.Ed448.AArch64.SignCached.reduceK_step hL hc) fun _ hu => ⟨hu.1, trivial⟩)
  have ma := mulAdd_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := mulAddArgs)
    (by decide) (by simp [mulAddArgs, aR, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fH, fS, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (VG.Proof.Ed448.AArch64.SignCached.mulAddVal L)
    (fun hm hc _ p hp => by
      simp only [mulAddArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc hm _
      · exact VG.Proof.Ed448.AArch64.SignCached.outS_src hL hc hm _
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (hL.oc.sub_left (VG.Proof.Ed448.AArch64.SignCached.outS_within L).sub) (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide)) (VG.Proof.Ed448.AArch64.SignCached.fr_scr hL (by decide))
    (.inr ⟨L.OUT, by simp [Lay.env], VG.Proof.Ed448.AArch64.SignCached.outS_within L⟩) (.inl ⟨fH, rfl, show fH + 57 ≤ 256 by decide⟩)
    (.inl ⟨fS, rfl, show fS + 57 ≤ 256 by decide⟩) (VG.Proof.Ed448.AArch64.SignCached.outS_writable L) (VG.Proof.Ed448.AArch64.SignCached.scr_writable L) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (VG.Proof.Ed448.AArch64.SignCached.mulAdd_step hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  have wp := block_ct (V := L.env) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) ha₁ ha₂
    (P := fun _ => True) (Q := fun _ => True) (is := wipe) (by taint_decide)
    fun _ hc _ => WP.mono (VG.Proof.Ed448.AArch64.SignCached.wipe_step hL hc) fun _ hu => ⟨hu.1, trivial⟩
  exact (e.seq ((VG.Proof.Ed448.AArch64.SignCached.seedHash_ct v hL ha₁ ha₂).seq (pr.seq ((VG.Proof.Ed448.AArch64.SignCached.nonceHash_ct v hL ha₁ ha₂).seq (rr.seq (bs.seq
    ((VG.Proof.Ed448.AArch64.SignCached.chalHash_ct v hL ha₁ ha₂).seq (rk.seq (ma.seq wp))))))))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem lay_eq {s t : State} (hp : scLocal.pub s t) : VG.Proof.Ed448.AArch64.SignCached.lay s = VG.Proof.Ed448.AArch64.SignCached.lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  simp only [VG.Proof.Ed448.AArch64.SignCached.lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, h3, h4, h5, h6, h7]

theorem signCached_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    ConstantTime isa scLocal.pre scLocal.pub (signCachedWith v.callee) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed448.AArch64.SignCached.signCached_ok_body v hb hs hp) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed448.AArch64.SignCached.lay_eq hp
    have hq : VG.Proof.Ed448.AArch64.SignCached.Ctx0 (VG.Proof.Ed448.AArch64.SignCached.lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) := he ▸ VG.Proof.Ed448.AArch64.SignCached.entry_ctx ht hqb
    have hqa : VG.Proof.Ed448.AArch64.SignCached.Args (VG.Proof.Ed448.AArch64.SignCached.lay s) q.mem := he ▸ VG.Proof.Ed448.AArch64.SignCached.entry_args hqb
    have hq6 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x6 = (VG.Proof.Ed448.AArch64.SignCached.lay s).len := he ▸ VG.Proof.Ed448.AArch64.SignCached.entry_x6 hqb
    have hq7 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x7 = (VG.Proof.Ed448.AArch64.SignCached.lay s).scr := he ▸ VG.Proof.Ed448.AArch64.SignCached.entry_x7 hqb
    exact ⟨(VG.Proof.Ed448.AArch64.SignCached.body_ct v hb (VG.Proof.Ed448.AArch64.SignCached.lay_ok hs) (VG.Proof.Ed448.AArch64.SignCached.entry_args hpa) hqa _ _ _ _ _ _
      ⟨⟨VG.Proof.Ed448.AArch64.SignCached.entry_ctx hs hpa, VG.Proof.Ed448.AArch64.SignCached.entry_x6 hpa, VG.Proof.Ed448.AArch64.SignCached.entry_x7 hpa⟩, ⟨hq, hq6, hq7⟩⟩ ea eb).1, trivial⟩

/-! ## A state satisfying the precondition -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey VG.Proof.Ed448.AArch64.SignCached.satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [VG.Proof.Ed448.AArch64.SignCached.satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else VG.Proof.Ed448.AArch64.SignCached.satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt VG.Proof.Ed448.AArch64.SignCached.satMem 0x2000 57 = VG.Proof.Ed448.AArch64.SignCached.satSeed := by
  unfold VG.Proof.Ed448.AArch64.SignCached.satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  simp only [VG.Proof.Ed448.AArch64.SignCached.satMem, ha, show 0x2000 + i < 0x3000 from by omega, true_or, ↓reduceIte]

theorem sat_key : Spec.Ed448.bytesAt VG.Proof.Ed448.AArch64.SignCached.satMem 0x3000 57 = VG.Proof.Ed448.AArch64.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, VG.Proof.Ed448.AArch64.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed448.AArch64.SignCached.satMem, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega, ↓reduceIte, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x5 => 0x5000 | .x7 => 0x10000
    | _ => 0
  sp := 0x20000
  mem := VG.Proof.Ed448.AArch64.SignCached.satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed448.signCachedContract AArch64.abi 352).pre s := by
  refine ⟨VG.Proof.Ed448.AArch64.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, VG.Proof.Ed448.AArch64.SignCached.satState]
    sig_and_intros
    · decide +kernel
    · change Spec.Ed448.bytesAt VG.Proof.Ed448.AArch64.SignCached.satMem 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt VG.Proof.Ed448.AArch64.SignCached.satMem 0x2000 57)
      rw [VG.Proof.Ed448.AArch64.SignCached.sat_seed, VG.Proof.Ed448.AArch64.SignCached.sat_key]
      rfl
    · decide

theorem signCached_implies : scLocal.Implies (Spec.Ed448.signCachedContract AArch64.abi 352) where
  pre := by
    sig_implies_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.AArch64.SignCached.scLocal, below, AArch64.abi, AArch64.argRegs]
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.AArch64.SignCached.scLocal, below, AArch64.abi, AArch64.argRegs]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.AArch64.SignCached.scLocal, below, AArch64.abi, AArch64.argRegs]
  sat := VG.Proof.Ed448.AArch64.SignCached.sat

theorem signCached_verified (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    Verified AArch64.target (signCachedWith v.callee) (Spec.Ed448.signCachedContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed448.AArch64.SignCached.signCached_ok v hb h) (VG.Proof.Ed448.AArch64.SignCached.signCached_ct v hb)
      (.refl signCached_implies.sat_left))
    VG.Proof.Ed448.AArch64.SignCached.signCached_implies

end VG.Proof.Ed448.AArch64.SignCached

end
