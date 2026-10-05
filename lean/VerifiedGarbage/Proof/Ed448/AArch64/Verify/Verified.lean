import VerifiedGarbage.Impl.Ed448.AArch64.Verify
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Verify.Layout`. -/
section

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
open VG.Proof.Ed448.AArch64.Whole (Env WCtx sigWord)
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
    s.rd = [pk, ctx, msg, sig] ∧ s.wr = [scr] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 114 ≤ 2 ^ 64 ∧
      (s.gpr .x6).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat
  post s t := t.gpr .x0 = if Spec.Ed448.verify (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x5) 114) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6

structure Lay where
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  sig : Addr
  scr : Addr
  E : Addr

namespace Lay
variable (L : VG.Proof.Ed448.AArch64.Verify.Lay)
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig, 114⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.E, 336⟩

/-- The saved argument `j`. -/
def arg (j : Nat) : Addr :=
  match j with | 0 => L.pk | 1 => L.ctx | 2 => L.ctxLen | 3 => L.msg | 4 => L.len | _ => L.sig

def inputs : List Region := [L.PK, L.CTX, L.MSG, L.SIG]

/-- The frame's body: it reads the inputs and the saved arguments, writes
`scratch`, and keeps `scratch` and the header of `dom4` in its locals. -/
def env : VG.Proof.Ed448.AArch64.Whole.Env where
  E := L.E
  ins := L.inputs ++ [ARGS L.E]
  outs := [L.SCR]
  ls := [(fScr, L.scr), (fHdr, sigWord), (fHdr + 8, L.ctxLen <<< 8)]

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

end Lay

theorem frame_sub (L : VG.Proof.Ed448.AArch64.Verify.Lay) : Region.Sub (FR L.E) L.STK := Region.sub_prefix (by decide : 256 ≤ 336)

theorem env_ok {L : VG.Proof.Ed448.AArch64.Verify.Lay} (hL : L.Ok) : L.env.Ok where
  args := by simp [Lay.env]
  ls := by simp [Lay.env, fScr, fHdr]
  fo := by
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.kc.sub_left (VG.Proof.Ed448.AArch64.Verify.frame_sub L)
  co := by
    intro R hR
    simp only [Lay.env, List.mem_singleton] at hR
    subst hR
    exact hL.ck
  e16 := hL.e16

/-- The layout of a call from `s`. -/
def lay (s : State) : VG.Proof.Ed448.AArch64.Verify.Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6,
    VG.Proof.Ed25519.AArch64.Whole.base s⟩

theorem lay_ok {s : State} (h : vLocal.pre s) (hc : (s.gpr .x2).toNat < 256) : (VG.Proof.Ed448.AArch64.Verify.lay s).Ok := by
  obtain ⟨_, _, pc, cc, mc, sc, kp, kx, km, ks, kc, np, ns, nc, hsp⟩ := h
  have st := VG.Proof.Ed25519.AArch64.Whole.stk_sub s
  have ck := VG.Proof.Ed25519.AArch64.Whole.ck_sub s
  exact ⟨pc, cc, mc, sc, kp.sub_left st, kx.sub_left st, km.sub_left st, ks.sub_left st, kc.sub_left st,
    kp.sub_left ck, kx.sub_left ck, km.sub_left ck, ks.sub_left ck, kc.sub_left ck, np, ns, nc,
    VG.Proof.Ed25519.AArch64.Whole.base_16 hsp, hc⟩

end VG.Proof.Ed448.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Verify.Body`. -/
section

/-!
# Ed448 verification on AArch64: the frame's body

From the saved arguments (`Args`) and `scratch` in `x6`: the entry keeps
`scratch` and the header of `dom4` in the locals (`entry_ok`), the hash
`H(dom4(0, C) ‖ R ‖ A ‖ M)` is squeezed into the locals (`hash_ok`), reduced
into `k` (`reduce_step`), and `x0` is the verification equation's result
(`body_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS keep hdr)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue readW_eq_read)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

variable {L : VG.Proof.Ed448.AArch64.Verify.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The saved arguments. -/
def Args (L : VG.Proof.Ed448.AArch64.Verify.Lay) (m : Mem) : Prop := ∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.arg j

abbrev Ctx0 (L : VG.Proof.Ed448.AArch64.Verify.Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx L.E g vec m₀ L.env.ins L.env.outs t

theorem args_sub (L : VG.Proof.Ed448.AArch64.Verify.Lay) : Region.Sub (ARGS L.E) L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

/-- What the body may write misses the saved arguments. -/
theorem args_apart (hL : L.Ok) : ∀ r ∈ L.env.outs ++ [FR L.E, CK L.E], (ARGS L.E).Disjoint r := by
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.kc.sub_left (VG.Proof.Ed448.AArch64.Verify.args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

theorem arg_word (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.Verify.Ctx0 L g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.Verify.Args L m₀) {j : Nat} (hj : j < 6) :
    t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * j)) 8 = L.arg j := by
  rw [← readW_eq_read, ← ha j hj]
  exact hc.frame.readW (r := ARGS L.E) (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega)
    (by decide)) (VG.Proof.Ed448.AArch64.Verify.args_apart hL) (by decide)

theorem arg_src (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.Verify.Ctx0 L g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.Verify.Args L m₀) {j : Nat} (hj : j < 6)
    (x0 : BitVec 64) : srcValue L.E t.mem x0 (.val (.caller j 0)) = L.arg j := by
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value]
  rw [VG.Proof.Ed448.AArch64.Verify.arg_word hL hc ha hj, BitVec.add_zero]

/-- An input's bytes, as on entry. -/
theorem in_bytes (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.Verify.Ctx0 L g vec m₀ t) {R : Region} (hR : R ∈ L.inputs)
    {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt t.mem R.base n = Spec.Sha3.bytesAt m₀ R.base n := by
  unfold Spec.Sha3.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := R) ?_ hl (by
    have := List.mem_range.mp hi; omega)
  simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hR
  simp only [Lay.env, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pc, hL.cc, hL.mc, hL.sc, (hL.kp.sub_left (VG.Proof.Ed448.AArch64.Verify.frame_sub L)).symm, (hL.kx.sub_left (VG.Proof.Ed448.AArch64.Verify.frame_sub L)).symm,
    (hL.km.sub_left (VG.Proof.Ed448.AArch64.Verify.frame_sub L)).symm, (hL.ks.sub_left (VG.Proof.Ed448.AArch64.Verify.frame_sub L)).symm, hL.cp.symm, hL.cx.symm,
    hL.cm.symm, hL.cs.symm]

/-- `scratch` kept, and the header of `dom4`. -/
theorem entry_ok (hL : L.Ok) (hc : VG.Proof.Ed448.AArch64.Verify.Ctx0 L g vec m₀ t) (ha : VG.Proof.Ed448.AArch64.Verify.Args L m₀) (h6 : t.gpr .x6 = L.scr) :
    WP isa (.block entry) t fun u => WCtx L.env g vec m₀ u := by
  have hfr : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  rw [entry, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x6) (d := fScr) (by decide)
    ⟨_, hfr, Offset.contains_base _ (by decide) (by decide)⟩) fun a ⟨ka, _, am⟩ => ?_
  have hfa : (⟨a.sp, 256⟩ : Region) ∈ a.wr := by rw [ka.sp, ka.wr]; exact hfr
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.hdr_ok (d := fHdr) (j := 2) (by decide) (by decide) hfa (by
    rw [ka.rd, ka.wr, ka.sp, hc.rd, hc.wr, hc.sp]
    exact ⟨ARGS L.E, List.mem_append_left _ (by simp [Lay.env]),
      Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)⟩)) fun u ⟨ku, um⟩ => ?_
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x6 ≠ .x15), h6, hc.sp] at am
  rw [ka.sp, hc.sp] at um
  have hread : a.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 2)) 8 = L.ctxLen := by
    rw [am, VG.Proof.Ed448.AArch64.Whole.read_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))]
    exact VG.Proof.Ed448.AArch64.Verify.arg_word hL hc ha (j := 2) (by decide)
  rw [hread] at um
  have hf : Frame [FR L.E] t.mem u.mem := by
    rw [um, am]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_)
      |>.writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base _ (by decide) (by decide)
    · exact Offset.contains_base _ (by decide) (by decide)
    · exact Offset.contains_base _ (by decide) (by decide)
  refine ⟨hc.of_frame (ku.rd.trans ka.rd) (ku.wr.trans ka.wr) (ku.sp.trans ka.sp) (fun r hr _ => ?_)
    (fun r _ => by rw [ku.v, ka.v]) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl fun _ h => h), ?_⟩
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

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Verify.Hash`. -/
section

/-!
# Ed448 verification on AArch64: the hash

`H(dom4(0, C) ‖ R ‖ A ‖ M)` into the locals at `fH` (`hash_ok`): the state
zeroed, the header of `dom4` (kept in the locals), the context, `R`, the
public key and the message absorbed in turn, each from the position the
previous one returned, the padding, and 114 bytes squeezed.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue srcValid noRet ScrOk ST KS
  st_within ks_within kabs_chain kpad_ok ksqz_ok zeroSt_ok repr_nil hdr_bytes shake256_eq ofNat_toNat64
  readW_eq_read Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK ck_frame)

variable {L : VG.Proof.Ed448.AArch64.Verify.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : VG.Proof.Ed448.AArch64.Verify.Lay) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- What is hashed: `dom4(0, C) ‖ R ‖ A ‖ M`. -/
abbrev hashIn (L : VG.Proof.Ed448.AArch64.Verify.Lay) (m : Mem) : List Byte :=
  VG.Proof.Ed448.AArch64.Verify.hdrBytes L ++ Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ Spec.Sha3.bytesAt m L.sig 57 ++
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
  .inr ⟨R, by simp [Lay.env, hR], VG.Proof.Ed448.AArch64.Verify.within_self R.base R.len⟩

/-- The hash. -/
theorem hash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : VG.Proof.Ed448.AArch64.Verify.Args L m₀) :
    WP isa (Impl.Ed448.AArch64.Verify.hash v.callee) t fun u => WCtx L.env g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 = Spec.Sha3.shake256 (VG.Proof.Ed448.AArch64.Verify.hashIn L m₀) 114 := by
  have hV := VG.Proof.Ed448.AArch64.Verify.env_ok hL
  have hs := VG.Proof.Ed448.AArch64.Verify.scrOk hL
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, _, hz₁⟩ => ?_)
  -- The header.
  have k0 := hc₁.2 (fHdr, sigWord) (by simp [Lay.env])
  have k8 := hc₁.2 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  have hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = VG.Proof.Ed448.AArch64.Verify.hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (VG.Proof.Ed448.AArch64.Verify.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.Verify.fr_ks hL (by decide)) (ck_frame (by decide))
    (VG.Proof.Ed448.AArch64.Whole.repr_nil hz₁)) fun t₂ ⟨hc₂, _, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  -- The context.
  have a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := VG.Proof.Ed448.AArch64.Verify.arg_src hL hc₂.1 ha (j := 1) (by decide) _
  have a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (VG.Proof.Ed448.AArch64.Verify.arg_src hL hc₂.1 ha (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (VG.Proof.Ed448.AArch64.Verify.in_readable L.CTX (by simp [Lay.inputs])) (hL.cc.sub_right (st_within L.scr).sub)
    (hL.cc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, _, hr₃, hx₃⟩ => ?_)
  have eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    VG.Proof.Ed448.AArch64.Verify.in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  -- `R`.
  have a5 : srcValue L.env.E t₃.mem (t₃.gpr .x0) aSig = L.sig := VG.Proof.Ed448.AArch64.Verify.arg_src hL hc₃.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := aSig) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a5 rfl hx₃ (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide))) hr₃)
    fun t₄ ⟨hc₄, _, hr₄, hx₄⟩ => ?_)
  have eS : Spec.Sha3.bytesAt t₃.mem L.sig 57 = Spec.Sha3.bytesAt m₀ L.sig 57 :=
    VG.Proof.Ed448.AArch64.Verify.in_bytes hL hc₃.1 (R := L.SIG) (by simp [Lay.inputs]) (show 57 ≤ 114 by decide) (show 114 ≤ 2 ^ 64 by decide)
  rw [eS] at hr₄ hx₄
  -- The public key.
  have a0 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aPk = L.pk := VG.Proof.Ed448.AArch64.Verify.arg_src hL hc₄.1 ha (j := 0) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aPk) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a0 rfl hx₄ (by decide)
    (VG.Proof.Ed448.AArch64.Verify.in_readable L.PK (by simp [Lay.inputs])) (hL.pc.sub_right (st_within L.scr).sub)
    (hL.pc.sub_right (ks_within L.scr).sub) hL.cp hr₄) fun t₅ ⟨hc₅, _, hr₅, hx₅⟩ => ?_)
  have eP : Spec.Sha3.bytesAt t₄.mem L.pk 57 = Spec.Sha3.bytesAt m₀ L.pk 57 :=
    VG.Proof.Ed448.AArch64.Verify.in_bytes hL hc₄.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eP] at hr₅ hx₅
  -- The message.
  have a3 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aMsg = L.msg := VG.Proof.Ed448.AArch64.Verify.arg_src hL hc₅.1 ha (j := 3) (by decide) _
  have a4 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aLen = BitVec.ofNat 64 L.len.toNat :=
    (VG.Proof.Ed448.AArch64.Verify.arg_src hL hc₅.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₅ (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a3 a4
    hx₅ L.len.isLt (VG.Proof.Ed448.AArch64.Verify.in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₅) fun t₆ ⟨hc₆, _, hr₆, hx₆⟩ => ?_)
  have eM : Spec.Sha3.bytesAt t₅.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    VG.Proof.Ed448.AArch64.Verify.in_bytes hL hc₅.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
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
    (VG.Proof.Ed448.AArch64.Verify.fr_st hL (by decide)) (VG.Proof.Ed448.AArch64.Verify.fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, _, hb⟩ => ⟨hu, ?_⟩
  rw [hb, hst, ← VG.Proof.Ed448.AArch64.Whole.shake256_eq]

end VG.Proof.Ed448.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Verify.Correct`. -/
section

/-!
# Ed448 verification on AArch64: the frame's body

After the hash: `k`, the hash reduced modulo `L` (`reduce_step`), and the
verification equation's result in `x0` (`equation_step`), for the inputs as
on entry (`body_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call equation_call
  Readable Writable Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

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

theorem equation_step (hQ : Proof.Ed448.AArch64.EqOk) (hL : L.Ok)
    (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS equationArgs "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation) t fun u =>
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
  refine WP.mono (equation_call hQ hV hu h0 h1 h2 h3 hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L)) fun w ⟨hw, _, hx⟩ => ⟨hw, ?_⟩
  have eP : Spec.Ed448.bytesAt u.mem L.pk 57 = Spec.Ed448.bytesAt m₀ L.pk 57 :=
    in_bytes hL hu.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  have eS : Spec.Ed448.bytesAt u.mem L.sig 114 = Spec.Ed448.bytesAt m₀ L.sig 114 :=
    in_bytes hL hu.1 (R := L.SIG) (by simp [Lay.inputs]) (Nat.le_refl _) (show 114 ≤ 2 ^ 64 by decide)
  rw [hx, eP, eS, hm]

/-- The frame's body: `x0` is the verification equation's result for the
reduced hash. -/
theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk)
    (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.scr) :
    WP isa (body v.callee) t fun u => Ctx0 L g vec m₀ u ∧
      u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57) (Spec.Ed448.bytesAt m₀ L.sig 114)
        (Spec.Ed448.scalarReduce (Spec.Sha3.shake256 (hashIn L m₀) 114)) then 1 else 0 := by
  refine WP.seq (WP.mono (entry_ok hL hc ha h6) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (hash_ok v hL hc₁ ha) fun t₂ ⟨hc₂, hh₂⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step hL hc₂) fun t₃ ⟨hc₃, hk₃⟩ => ?_)
  refine WP.mono (equation_step hQ hL hc₃ ha) fun u ⟨hu, hx⟩ => ⟨hu.1, ?_⟩
  rw [hx, hk₃, show Spec.Ed448.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 =
    Spec.Sha3.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 from rfl, hh₂]

end VG.Proof.Ed448.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main`. -/
section

/-!
# Ed448 verification on AArch64: the whole function

`vg_ed448_verify` meets `vLocal` and the ABI (`verify_ok`), for any
implementation `v` of the Keccak permutation, given that
`vg_ed448_verify_equation` meets its contract (`EqOk`, `VerifyLocal.lean`):
a context of 256 bytes or more returns 0; otherwise the frame
(`Proof.Ed25519.AArch64.Whole.wrap_ok`) runs the body, whose result is
RFC 8032's verification of the inputs as on entry.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Proof.Ed25519.AArch64.Whole (Saved entered bodyRd bodyWr)
open VG.Proof.Ed448.AArch64.Whole (sha3_bytesAt_length)

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨_, _, Exec.iteT hc e, hq⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨_, _, Exec.iteF hc e, hq⟩

/-- What `lsr x9, x2, #8` does. -/
abbrev LsrPost (s t : State) : Prop :=
  t.gpr .x9 = s.gpr .x2 >>> 8 ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
    t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v

theorem lsr_ok (s : State) : WP isa (.block [.lsr .x .x9 .x2 8]) s (LsrPost s) := by
  apply WP.of_runBlock
  simp only [LsrPost, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, Nat.reduceLT,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl, rfl⟩

theorem lsr_pre {s t : State} (h : vLocal.pre s) (ht : LsrPost s t) : vLocal.pre t := by
  obtain ⟨_, e, _, trd, twr, tsp, _⟩ := ht
  simp only [vLocal, e _ (by decide : Reg.x0 ≠ .x9), e _ (by decide : Reg.x1 ≠ .x9),
    e _ (by decide : Reg.x2 ≠ .x9), e _ (by decide : Reg.x3 ≠ .x9), e _ (by decide : Reg.x4 ≠ .x9),
    e _ (by decide : Reg.x5 ≠ .x9), e _ (by decide : Reg.x6 ≠ .x9), trd, twr, tsp]
  exact h

theorem lsr_pub {s₁ s₂ t₁ t₂ : State} (h : vLocal.pub s₁ s₂) (h₁ : LsrPost s₁ t₁) (h₂ : LsrPost s₂ t₂) :
    vLocal.pub t₁ t₂ := by
  obtain ⟨_, e₁, _, _, _, sp₁, _⟩ := h₁
  obtain ⟨_, e₂, _, _, _, sp₂, _⟩ := h₂
  simp only [vLocal, e₁ _ (by decide : Reg.x0 ≠ .x9), e₁ _ (by decide : Reg.x1 ≠ .x9),
    e₁ _ (by decide : Reg.x2 ≠ .x9), e₁ _ (by decide : Reg.x3 ≠ .x9), e₁ _ (by decide : Reg.x4 ≠ .x9),
    e₁ _ (by decide : Reg.x5 ≠ .x9), e₁ _ (by decide : Reg.x6 ≠ .x9),
    e₂ _ (by decide : Reg.x0 ≠ .x9), e₂ _ (by decide : Reg.x1 ≠ .x9),
    e₂ _ (by decide : Reg.x2 ≠ .x9), e₂ _ (by decide : Reg.x3 ≠ .x9), e₂ _ (by decide : Reg.x4 ≠ .x9),
    e₂ _ (by decide : Reg.x5 ≠ .x9), e₂ _ (by decide : Reg.x6 ≠ .x9), sp₁, sp₂]
  exact h

theorem lsr_zero {s t : State} (ht : LsrPost s t) : t.gpr .x9 = 0 ↔ (s.gpr .x2).toNat < 256 := by
  rw [ht.1]
  constructor
  · intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    change _ = 0 at this
    omega
  · intro hc
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; show _ = 0; omega

theorem lsr_x2 {s t : State} (ht : LsrPost s t) : t.gpr .x2 = s.gpr .x2 := ht.2.1 _ (by decide)

theorem movz0_ok (s : State) :
    WP isa (.block [.movz .x .x0 0 0]) s fun t => t.gpr .x0 = 0 ∧
      (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl⟩

theorem body_depth (v : Proof.Sha3.AArch64.Permutation) : (body v.callee).aarch64Depth ≤ 1 := by
  have ha := v.absorb_depth
  have hp := v.pad_depth
  have hs := v.squeeze_depth
  have hr := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.reduce_noFrames
  have he := VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames VG.Proof.Ed448.AArch64.Whole.equation_noFrames
  simp only [body, Impl.Ed448.AArch64.Verify.hash, Impl.Ed448.AArch64.Whole.zeroSt,
    Impl.Ed448.AArch64.Whole.kabs, Impl.Ed448.AArch64.Whole.kpad, Impl.Ed448.AArch64.Whole.ksqz,
    Impl.Ed448.AArch64.Whole.callS, Code.aarch64Depth, Nat.max_le, ha, hp, hs, hr, he]
  omega

/-- The hash of the specification, as the body computes it. -/
theorem verify_eq (pk ctx msg sig : List Byte) (hc : ctx.length < 256) :
    Spec.Ed448.verify pk ctx msg sig = Spec.Ed448.verifyEquation pk sig (Spec.Ed448.scalarReduce
      (Spec.Sha3.shake256 ("SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++
        [BitVec.ofNat 8 0, BitVec.ofNat 8 ctx.length] ++ ctx ++ sig.take 57 ++ pk ++ msg) 114)) := by
  simp only [Spec.Ed448.verify, Spec.Ed448.hash, Spec.Ed448.dom4, List.append_assoc,
    show ctx.length ≤ 255 from by omega, decide_true, Bool.true_and]

/-- An input's bytes after the frame's writes, as on entry. -/
theorem frame_bytes {m m' : Mem} {S R : Region} (hf : Frame [S] m m') (hd : S.Disjoint R) {n : Nat}
    (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' R.base n = Spec.Sha3.bytesAt m R.base n := by
  unfold Spec.Sha3.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := R) ?_ hl (by have := List.mem_range.mp hi; omega)
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact hd.symm

theorem ed448_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ed448.bytesAt m p n = Spec.Sha3.bytesAt m p n := rfl

theorem take57' (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Sha3.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, ← List.map_take, List.take_range]

theorem entry_ctx {s p : State} (h : vLocal.pre s) (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    Ctx0 (lay s) s.gpr s.v p.mem (p.withRegions (bodyRd s) (bodyWr s)) := by
  have hc := VG.Proof.Ed25519.AArch64.Whole.saved_ctx hp
  simpa only [bodyRd, bodyWr, h.1, h.2.1, Ctx0, Lay.env, Lay.inputs, Lay.PK, Lay.CTX, Lay.MSG,
    Lay.SIG, Lay.SCR, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) : Args (lay s) p.mem := fun j hj => by
  have hw := VG.Proof.Ed25519.AArch64.Whole.saved_words hp hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_x6 {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (entered s) 6 p) :
    (p.withRegions (bodyRd s) (bodyWr s)).gpr .x6 = (lay s).scr :=
  hp.step.regs .x6 (by decide)

theorem body_ctx {s p u : State} (h : vLocal.pre s) (hu : Ctx0 (lay s) s.gpr s.v p.mem u) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx (VG.Proof.Ed25519.AArch64.Whole.base s) s.gpr s.v p.mem (bodyRd s)
      s.wr u := by
  simpa only [bodyRd, bodyWr, h.1, h.2.1, Ctx0, Lay.env, Lay.inputs, Lay.PK, Lay.CTX, Lay.MSG,
    Lay.SIG, Lay.SCR, lay, List.cons_append, List.nil_append] using hu

theorem verify_ok (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk)
    {s : State} (h : vLocal.pre s) :
    WP isa (verifyWith v.callee) s fun u => abiPreserved s u ∧ vLocal.post s u := by
  refine WP.seq (WP.mono (lsr_ok s) fun t ht => ?_)
  have ⟨_, tg, tm, _, _, tsp, tv⟩ := ht
  have e : ∀ r, r ≠ .x9 → t.gpr r = s.gpr r := tg
  have hpre : vLocal.pre t := lsr_pre h ht
  have hpost : ∀ u, vLocal.post t u → vLocal.post s u := fun u hu => by
    simp only [vLocal, e _ (by decide : Reg.x0 ≠ .x9), e _ (by decide : Reg.x1 ≠ .x9),
      e _ (by decide : Reg.x2 ≠ .x9), e _ (by decide : Reg.x3 ≠ .x9), e _ (by decide : Reg.x4 ≠ .x9),
      e _ (by decide : Reg.x5 ≠ .x9), tm] at hu
    exact hu
  have habi : ∀ u, abiPreserved t u → abiPreserved s u := fun u ⟨hg, hsp, hv⟩ =>
    ⟨fun r hr => (hg r hr).trans (tg r (by rintro rfl; simp [preserved] at hr)), hsp.trans tsp,
      fun r hr => by rw [hv r hr, tv]⟩
  have hc2 : (t.gpr .x2).toNat = (s.gpr .x2).toNat := by rw [e _ (by decide)]
  by_cases hc : (s.gpr .x2).toNat < 256
  · -- The frame and the body.
    have h9 : t.gpr .x9 = 0 := (lsr_zero ht).2 hc
    refine wp_ite_t (by simp [eval, State.read, h9]) ?_
    have hc' : (t.gpr .x2).toNat < 256 := hc2 ▸ hc
    have hL := lay_ok hpre hc'
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.wrap_ok (body_depth v) hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (fun r hr => by
        rw [hpre.2.1] at hr; simp only [List.mem_singleton] at hr; subst hr; exact hpre.2.2.2.2.2.2.2.2.2.2.1)
      (P := fun m _ x0 => x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m (t.gpr .x0) 57)
        (Spec.Ed448.bytesAt m (t.gpr .x5) 114) (Spec.Ed448.scalarReduce
          (Spec.Sha3.shake256 (hashIn (lay t) m) 114)) then 1 else 0) fun p hp => ?_)
      fun u ⟨hu, m, hf, hx⟩ => ⟨habi u hu, hpost u ?_⟩
    · refine WP.mono (body_ok v hQ hL (entry_ctx hpre hp) (entry_args hp) (entry_x6 hp))
        fun u ⟨hu, hx⟩ => ⟨body_ctx hpre hu, hx⟩
    · have hb : ∀ R ∈ (lay t).inputs, ∀ n ≤ R.len, R.len ≤ 2 ^ 64 →
          Spec.Sha3.bytesAt m R.base n = Spec.Sha3.bytesAt t.mem R.base n := by
        intro R hR n hn hl
        refine frame_bytes hf ?_ hn hl
        simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl | rfl | rfl
        exacts [hL.kp, hL.kx, hL.km, hL.ks]
      have hpk := hb (lay t).PK (by simp [Lay.inputs]) 57 (Nat.le_refl _) (by change 57 ≤ 2 ^ 64; decide)
      have hcx := hb (lay t).CTX (by simp [Lay.inputs]) (t.gpr .x2).toNat (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _))
      have hms := hb (lay t).MSG (by simp [Lay.inputs]) (t.gpr .x4).toNat (Nat.le_refl _) (Nat.le_of_lt (BitVec.isLt _))
      have hsg := hb (lay t).SIG (by simp [Lay.inputs]) 114 (Nat.le_refl _) (by change 114 ≤ 2 ^ 64; decide)
      have hs57 := hb (lay t).SIG (by simp [Lay.inputs]) 57 (by change 57 ≤ 114; decide) (by change 114 ≤ 2 ^ 64; decide)
      simp only [lay] at hpk hcx hms hsg hs57
      show u.gpr .x0 = _
      rw [hx, verify_eq _ _ _ _ (by rw [ed448_bytesAt, sha3_bytesAt_length]; exact hc')]
      simp only [ed448_bytesAt, take57', sha3_bytesAt_length, hashIn, hdrBytes, lay, List.append_assoc,
        hpk, hcx, hms, hsg, hs57]
  · -- A context of 256 bytes or more.
    have h9 : t.gpr .x9 ≠ 0 := fun h0 => hc ((lsr_zero ht).1 h0)
    refine wp_ite_f (by simp only [eval, State.read, Option.some.injEq, beq_eq_false_iff_ne]; exact h9) ?_
    refine WP.mono (movz0_ok t) fun u ⟨u0, ug, usp, uv⟩ => ⟨habi u ⟨fun r hr => ug r (by
      rintro rfl; simp [preserved] at hr), usp, fun r _ => by rw [uv]⟩, hpost u ?_⟩
    show u.gpr .x0 = _
    rw [u0, Spec.Ed448.verify, ed448_bytesAt, sha3_bytesAt_length]
    simp only [show ¬ (t.gpr .x2).toNat ≤ 255 by omega, decide_false, Bool.false_and]
    rfl

end VG.Proof.Ed448.AArch64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified`. -/
section

/-!
# Ed448 verification on AArch64: `Verified`

Correctness including the ABI (`verify_ok`), for any implementation `v` of
the Keccak permutation, given `EqOk` (which the generic file passes in, from
`VerifyVerified.lean`). Constant time in everything but the pointers and lengths:
the branch on `ctxlen` is on a public length; in the frame's body, two runs
whose pointers and lengths agree have the same layout, so they are related
by `Whole.Two`. The blocks address only the stack and `scratch`, from
registers that agree (the taint analysis); each call is of constant-time
code (the sponge functions for `v`, `vg_ed448_scalar_reduce`,
`vg_ed448_verify_equation`, all constant time in their buffers' contents)
whose public data, its pointers, lengths and the sponge's positions, agree.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Two WCtx srcValue zeroSt_ct kabs_ct kpad_ct ksqz_ct reduce_ct equation_ct
  ofNat_toNat64 st_within ks_within)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

/-- The arguments of `vg_ed448_scalar_reduce`. -/
def reduceVal (L : Lay) : Reg → Addr
  | .x0 => L.E + BitVec.ofNat 64 fK
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

/-- The arguments of `vg_ed448_verify_equation`. -/
def equationVal (L : Lay) : Reg → Addr
  | .x0 => L.pk
  | .x1 => L.sig
  | .x2 => L.E + BitVec.ofNat 64 fK
  | _ => L.scr

/-- The positions of the sponge after each absorption. -/
abbrev q1 : Nat := (0 + 10) % 136
abbrev q2 (L : Lay) : Nat := (q1 + L.ctxLen.toNat) % 136
abbrev q3 (L : Lay) : Nat := (q2 L + 57) % 136
abbrev q4 (L : Lay) : Nat := (q3 L + 57) % 136
abbrev q5 (L : Lay) : Nat := (q4 L + L.len.toNat) % 136

theorem hash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (Impl.Ed448.AArch64.Verify.hash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have z := zeroSt_ct hV hs ha₁ ha₂ (P := fun _ => True) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (by taint_decide)
  have k1 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := .val (.frame fHdr))
    (len := .val (.const 10)) (pos := .val (.const 0)) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl (by taint_decide) (P := fun _ => True)
    (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (q := 0) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (by decide) (by decide) (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  have k2 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aCtx)
    (len := aCtxLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.ctx) (n := L.ctxLen.toNat) (q := q1)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 1) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm)
    (fun _ _ hp => hp) (by decide) L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs]))
    (hL.cc.sub_right (st_within L.scr).sub) (hL.cc.sub_right (ks_within L.scr).sub) hL.cx
  have k3 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aSig)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.sig) (n := 57) (q := q2 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 5) (by decide) _) (fun _ _ _ => rfl)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide)))
  have k4 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aPk)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.pk) (n := 57) (q := q3 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 0) (by decide) _) (fun _ _ _ => rfl)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide) (in_readable L.PK (by simp [Lay.inputs]))
    (hL.pc.sub_right (st_within L.scr).sub) (hL.pc.sub_right (ks_within L.scr).sub) hL.cp
  have k5 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aMsg)
    (len := aLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.msg) (n := L.len.toNat) (q := q4 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 3) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) L.len.isLt (in_readable L.MSG (by simp [Lay.inputs]))
    (hL.mc.sub_right (st_within L.scr).sub) (hL.mc.sub_right (ks_within L.scr).sub) hL.cm
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := q5 L) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide))
  have q := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl)
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fScr, fHdr, fH]) (by simp [fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  exact z.seq (k1.seq (k2.seq (k3.seq (k4.seq (k5.seq (p.seq q))))))

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk)
    (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.scr) ∧ (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.scr))
      (body v.callee) fun _ _ => True := by
  have hV := env_ok hL
  have hs := scrOk hL
  have e : RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.scr) ∧ (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.scr))
      (.block entry) (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
    VG.Proof.Ed25519.AArch64.Whole.rel_wp
      (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide))
      (fun _ h => WP.mono (entry_ok hL h.1 ha₁ h.2) fun _ hu => ⟨hu, trivial⟩)
      (fun _ h => WP.mono (entry_ok hL h.1 ha₂ h.2) fun _ hu => ⟨hu, trivial⟩)
  have r := reduce_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceArgs)
    (by decide) (by simp [reduceArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fK, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (reduceVal L)
    (fun _ hc _ p hp => by
      simp only [reduceArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (k_apart L)) (scr_writable L) (Q := fun _ => True)
    (fun _ hc _ => WP.mono (reduce_step hL hc) fun _ hu => ⟨hu.1, trivial⟩)
  have q := equation_ct hQ hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := equationArgs)
    (by decide) (by simp [equationArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, aPk, aSig, fK, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (equationVal L)
    (fun hm hc _ p hp => by
      simp only [equationArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact arg_src hL hc.1 hm (j := 0) (by decide) _
      · exact arg_src hL hc.1 hm (j := 5) (by decide) _
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (equation_step hQ hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  exact (e.seq ((hash_ct v hL ha₁ ha₂).seq (r.seq q))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem lay_eq {s t : State} (hp : vLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, h6⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, h3, h4, h5, h6]

/-- The frame and its body, for a context shorter than 256 bytes. -/
theorem wrap_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk) :
    ConstantTime isa (fun s => vLocal.pre s ∧ (s.gpr .x2).toNat < 256) vLocal.pub
      (Impl.Ed25519.AArch64.Whole.wrap (body v.callee)) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v hQ (lay_ok hs.1 hs.2) (entry_ctx hs.1 hp) (entry_args hp) (entry_x6 hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx0 (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) := he ▸ entry_ctx ht.1 hqb
    have hqa : Args (lay s) q.mem := he ▸ entry_args hqb
    have hq6 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x6 = (lay s).scr := he ▸ entry_x6 hqb
    exact ⟨(body_ct v hQ (lay_ok hs.1 hs.2) (entry_args hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs.1 hpa, entry_x6 hpa⟩, ⟨hq, hq6⟩⟩ ea eb).1, trivial⟩

theorem verify_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk) :
    ConstantTime isa vLocal.pre vLocal.pub (verifyWith v.callee) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have hl := (RelCT.taint (A := taint) (P := fun s₁ s₂ => vLocal.pre s₁ ∧ vLocal.pre s₂ ∧ vLocal.pub s₁ s₂)
    (c := .block [.lsr .x .x9 .x2 8]) (Taint.ofRegs [.x2])
    (fun _ _ h => ⟨h.2.2.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst hr
      exact h.2.2.2.2.2.1⟩) (by taint_decide)).wpDep (F := LsrPost) fun s₁ s₂ _ => ⟨lsr_ok s₁, lsr_ok s₂⟩
  refine hl.seq (RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, h₁, h₂⟩ => ?_) ?_ ?_)
  · simp only [eval, State.read, h₁.1, h₂.1, hp.2.2.2.1]
  · intro a b ta tb a' b' ⟨⟨_, σ₁, σ₂, ⟨p₁, p₂, hp⟩, h₁, h₂⟩, hc⟩ ea eb
    have hz : ∀ {σ t : State}, LsrPost σ t → isa.eval (.zero .x .x9) t = some true →
        (t.gpr .x2).toNat < 256 := fun h hc => by
      rw [lsr_x2 h]
      refine (lsr_zero h).1 ?_
      simpa [eval, State.read] using hc
    have hc₂ : isa.eval (.zero .x .x9) b = some true := by
      rw [← hc]; simp only [eval, State.read, h₁.1, h₂.1, hp.2.2.2.1]
    exact ⟨wrap_ct v hQ _ _ _ _ _ _ ⟨lsr_pre p₁ h₁, hz h₁ hc⟩ ⟨lsr_pre p₂ h₂, hz h₂ hc₂⟩
      (lsr_pub hp h₁ h₂) ea eb, trivial⟩
  · exact VG.Proof.Ed25519.AArch64.Whole.block_rel
      (fun _ _ ⟨⟨_, _, _, ⟨_, _, hp⟩, h₁, h₂⟩, _⟩ => h₁.2.2.2.2.2.1.trans (hp.1.trans h₂.2.2.2.2.2.1.symm))
      (by taint_decide)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0 | .x3 => 0x3000 | .x4 => 0 | .x5 => 0x4000
    | .x6 => 0x6000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 114⟩]
  wr := [⟨0x6000, 8192⟩]

theorem verify_implies : vLocal.Implies (Spec.Ed448.verifyContract AArch64.abi 352) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, vLocal, below, AArch64.abi, AArch64.argRegs]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs]
    change t.gpr .x0 = _ at h
    rw [h]
    split <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨sp, -, h0, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨sp, h0, h1, h2, h3, h4, h5, h6⟩
  sat := by
    sig_implies_sat [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, vLocal, below, AArch64.abi, AArch64.argRegs]
      [satState] using satState

theorem verify_verified (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk) :
    Verified AArch64.target (verifyWith v.callee) (Spec.Ed448.verifyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verify_ok v hQ h) (verify_ct v hQ) (.refl verify_implies.sat_left))
    verify_implies

end VG.Proof.Ed448.AArch64.Verify

end
