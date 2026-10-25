module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcLay
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on AArch64: the call

`EM` as `vg_rsa_pkcs1_encrypt` builds it, then `pre` and `pre_len` (the
stack arguments 4 and 5, which no step changes) in `x2` and `x3`
(`callArgs_inv`), and the call of a precomputed public operation
(`pd_call`): the frame as after `vg_rsa_pkcs1_encrypt`'s call (`CalledF`),
and, if `pre` holds the values for `n`, its result in `out`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked PdOk PubLay pdCall pdRd)

/-- `pre` and `pre_len`, the words of the entry memory `m₀` at `Q + 1120`
and `Q + 1128`. -/
abbrev preW (L : Lay) (m₀ : Mem) : BitVec 64 := m₀.readW (L.Q + BitVec.ofNat 64 1120) 64
abbrev prlW (L : Lay) (m₀ : Mem) : BitVec 64 := m₀.readW (L.Q + BitVec.ofNat 64 1128) 64

/-- `pre` in a layout from the entry memory `m₀`. -/
structure PreOk (L : Lay) (m₀ : Mem) : Prop where
  hx : L.X = [⟨preW L m₀, (prlW L m₀).toNat * 8⟩]
  al : L.al = 48
  pl : (prlW L m₀).toNat = Spec.Rsa.precomputedWords L.k.toNat

theorem preW_layP (P : Nat) (s : State) : preW (layP P s) s.mem = stackArg s 4 := by
  show s.mem.readW (_ + BitVec.ofNat 64 (1088 + 8 * 4)) 64 = _
  exact arg_mem

theorem prlW_layP (P : Nat) (s : State) : prlW (layP P s) s.mem = stackArg s 5 := by
  show s.mem.readW (_ + BitVec.ofNat 64 (1088 + 8 * 5)) 64 = _
  exact arg_mem

theorem preOk_of {P : Nat} {s : State} (hpl : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .x3).toNat) :
    PreOk (layP P s) s.mem :=
  ⟨by rw [preW_layP, prlW_layP]; rfl, rfl, by rw [prlW_layP]; exact hpl⟩

/-- The region of `pre`. -/
abbrev PRE (L : Lay) (m₀ : Mem) : Region := ⟨preW L m₀, (prlW L m₀).toNat * 8⟩

/-- A word of the stack arguments, as on entry. -/
theorem arg_keep {L : Lay} (hL : L.Ok) (hA : L.al = 48) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {t : State} (hc : Ctx L g vv m₀ t) {d : Nat} (h₁ : 1088 ≤ d) (h₂ : d + 8 ≤ 1136) :
    t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = m₀.readW (L.Q + BitVec.ofNat 64 d) 64 := by
  have hnQ := hL.nQa
  have hpQ := hL.pQ
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, 8⟩ L.ARGS := Offset.sub _ (by omega_arith) (by omega_arith)
  refine hc.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hL.oA.symm.sub_left hs
  · exact hL.sA.symm.sub_left hs
  · show Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 1088⟩
    rw [q_add L.Q L.P d]
    exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

theorem pre_in {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) (hp : PreOk L m₀) : PRE L m₀ ∈ t.rd := by
  rw [hc.rd, hp.hx]; simp

theorem pre_ok {L : Lay} (hL : L.Ok) {m₀ : Mem} (hp : PreOk L m₀) :
    (PRE L m₀).Disjoint L.OUT ∧ (PRE L m₀).Disjoint L.SCR ∧ L.STK.Disjoint (PRE L m₀) ∧
      (preW L m₀).toNat + (prlW L m₀).toNat * 8 ≤ 2 ^ 64 := by
  have h : PRE L m₀ ∈ L.X := by rw [hp.hx]; simp
  exact ⟨hL.xO _ h, hL.xS _ h, hL.xK _ h, hL.xw _ h⟩

/-- Before the call, with its arguments. -/
structure ReadyP (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  pre : PreOk L m₀
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.ol
  x2 : t.gpr .x2 = preW L m₀
  x3 : t.gpr .x3 = prlW L m₀
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.Q + BitVec.ofNat 64 oEM
  x7 : t.gpr .x7 = L.k
  em : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
    Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)
  z : t.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

/-- After the loads of `pre` and `pre_len`. -/
structure Loads (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  x2 : u.gpr .x2 = t.mem.readW (t.sp + BitVec.ofNat 64 1120) 64
  x3 : u.gpr .x3 = t.mem.readW (t.sp + BitVec.ofNat 64 1128) 64
  other : ∀ r, r ≠ .x2 → r ≠ .x3 → u.gpr r = t.gpr r

theorem loads_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 1120) 8)
    (h1 : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 1128) 8) :
    WP isa (.block [.ldrSp .x2 (arg 4), .ldrSp .x3 (arg 5)]) t (Loads t) := by
  apply WP.of_runBlock
  simp only [arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, exec, State.load,
    BitVec.setWidth_eq, Option.map_some, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceLT, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, h0, h1, read8, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq],
    by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq],
    fun r h2 h3 => by simp only [RegUpd.gpr_write, h2, h3, ite_false]⟩

theorem callArgs_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hp : PreOk L m₀) (hg : RegsOf L g) (h : MsgInv L g vv m₀ L.ml.toNat t) :
    WP isa (.block Impl.RsaPkcs1Enc.AArch64.Precomputed.callArgs) t (ReadyP L g vv m₀) := by
  unfold Impl.RsaPkcs1Enc.AArch64.Precomputed.callArgs
  rw [WP.block_append_iff]
  refine WP.mono (Enc.callArgs_inv hL hg h) fun t₁ h₁ => ?_
  have hc := h₁.ctx
  have hA := hp.al
  have := hL.nQa
  have i0 : InRegions (t₁.rd ++ t₁.wr) (t₁.sp + BitVec.ofNat 64 1120) 8 := by
    rw [hc.sp]; exact ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp,
      Offset.contains _ (by omega_arith) (by omega_arith) (by have := hL.al64; omega_arith)⟩
  have i1 : InRegions (t₁.rd ++ t₁.wr) (t₁.sp + BitVec.ofNat 64 1128) 8 := by
    rw [hc.sp]; exact ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp,
      Offset.contains _ (by omega_arith) (by omega_arith) (by have := hL.al64; omega_arith)⟩
  refine WP.mono (loads_ok i0 i1) fun u hu => ?_
  have go : ∀ r, r ≠ .x2 → r ≠ .x3 → u.gpr r = t₁.gpr r := hu.other
  refine ⟨hc.regs hu.rd hu.wr hu.sp hu.mem hu.v fun r hr _ => go r (mem_ne hr (by decide)) (mem_ne hr (by decide)),
    hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [go .x0 (by decide) (by decide), h₁.x0]
  · rw [go .x1 (by decide) (by decide), h₁.x1]
  · rw [hu.x2, hc.sp, arg_keep hL hA hc (by omega_arith) (by omega_arith)]
  · rw [hu.x3, hc.sp, arg_keep hL hA hc (by omega_arith) (by omega_arith)]
  · rw [go .x4 (by decide) (by decide), h₁.x4]
  · rw [go .x5 (by decide) (by decide), h₁.x5]
  · rw [go .x6 (by decide) (by decide), h₁.x6]
  · rw [go .x7 (by decide) (by decide), h₁.x7]
  · rw [hu.mem]; exact h₁.em
  · rw [hu.mem]; exact h₁.z

/-- `pre`'s words, as on entry. -/
theorem pre_words {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) (hp : PreOk L m₀) :
    Spec.Rsa.wordsAt t.mem (preW L m₀) (prlW L m₀).toNat = Spec.Rsa.wordsAt m₀ (preW L m₀) (prlW L m₀).toNat := by
  obtain ⟨pO, pS, pK, pw⟩ := pre_ok hL hp
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hc.frame.readW (r := PRE L m₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [pO, pS, pK.symm]

/-- What the precomputed public operation needs at the call. -/
theorem pd_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : ReadyP L g vv m₀ t) : PdOk L.P t := by
  have hc := h.ctx
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hk := hL.k1024
  have olk := hL.olk
  obtain ⟨pO, pS, pK, pw⟩ := pre_ok hL h.pre
  have hQ40 : (L.Q + BitVec.ofNat 64 oEM).toNat = L.Q.toNat + oEM := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by unfold oEM; omega_arith), Nat.mod_eq_of_lt (by unfold oEM; omega_arith)]
  have a0 : stackArg t 0 = L.scr := by
    show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [hc.sp]; exact hc.kept.scr
  have a1 : stackArg t 1 = L.sl := by
    show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [hc.sp]; exact hc.kept.sl
  have emS : Region.Sub L.EM L.STK := Lay.Ok.sub_stk (by unfold oEM; omega_arith)
  have arS : Region.Sub ⟨L.Q, 16⟩ L.STK := by
    have := Lay.Ok.sub_stk (L := L) (d := 0) (n := 16) (by omega_arith)
    rwa [show L.Q + BitVec.ofNat 64 0 = L.Q from BitVec.add_zero _] at this
  have frL : ∀ {d n : Nat}, d + n ≤ 1120 → Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, n⟩ L.LOW :=
    fun hd => hL.fr_low hd
  have qL : Region.Disjoint ⟨L.Q, 16⟩ L.LOW := by
    have := frL (d := 0) (n := 16) (by omega_arith)
    rwa [show L.Q + BitVec.ofNat 64 0 = L.Q from BitVec.add_zero _] at this
  have hl : PubLay L.Q L.P L.out (preW L m₀) L.e (L.Q + BitVec.ofNat 64 oEM) L.scr L.k.toNat
      ((prlW L m₀).toNat * 8) L.el.toNat L.k.toNat (L.sl.toNat * 8) :=
    ⟨hpQ, by omega_arith, pO.symm, hL.oE, hL.kO.symm.sub_right emS, hL.oS, hL.kO.symm.sub_right arS, pS, hL.eS,
      hL.kS.sub_left emS, (hL.kS.sub_left arS).symm, hL.kO.sub_left Lay.Ok.low_stk,
      pK.sub_left Lay.Ok.low_stk, hL.kE.sub_left Lay.Ok.low_stk, (frL (by unfold oEM; omega_arith)).symm,
      hL.kS.sub_left Lay.Ok.low_stk, qL.symm, hL.bO, pw, hL.bE, by rw [hQ40]; unfold oEM; omega_arith, hL.bS⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.sp, h.x0, h.x2, h.x4, h.x6, a0, h.x1, olk, h.x3, h.x5, h.x7, a1]; exact hl
  · simp only [pdRd]
    rw [h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, hc.sp, hc.rd, hc.wr]
    refine Covers.of_sub fun r hr => ?_
    have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨PRE L m₀, by rw [h.pre.hx]; simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, oEM, rfl, by show oEM + L.k.toNat ≤ frameBytes; unfold oEM frameBytes; omega_arith⟩
    · exact ⟨L.FR, by simp, 0, z _, by show 0 + 16 ≤ frameBytes; decide⟩
  · simp only [Proof.RsaPkcs1Sig.AArch64.pubWr]
    rw [h.x0, h.x1, a0, a1, hc.wr]
    refine Covers.of_sub fun r hr => ?_
    have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp [olk]⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩
  · rw [h.x1, olk]; exact hL.kv
  · rw [h.x3, h.x1, olk]; exact h.pre.pl
  · rw [h.x7, h.x1, olk]
  · rw [h.x5]; exact hL.el1
  · rw [h.x5, h.x1, olk]; exact hL.elk
  · rw [h.x1, olk, a1]; exact hL.slk

/-- Whether `pre` holds the values for `n`. -/
def Consistent (L : Lay) (m₀ : Mem) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) =
    some (Spec.Rsa.wordsAt m₀ (preW L m₀) (prlW L m₀).toNat)

/-- After the call. -/
structure CalledP (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t' : State) : Prop
    extends CalledF L g vv m₀ t' where
  out : Consistent L m₀ → Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
      (Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)))

theorem pd_call (c : PdChecked) {L : Lay} (hL : L.Ok) (hP : L.P = c.stack) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t : State} (h : ReadyP L g vv m₀ t) :
    WP isa (.call c.name c.code) t (CalledP L g vv m₀) := by
  have hc := h.ctx
  have hnQ := hL.nQ
  have hk := hL.k1024
  have hdp := c.depth
  have hpQ := hL.pQ
  have olk := hL.olk
  have hok := pd_ok hL h
  rw [hP] at hok hpQ
  have a0 : stackArg t 0 = L.scr := by
    show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [hc.sp]; exact hc.kept.scr
  have a1 : stackArg t 1 = L.sl := by
    show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [hc.sp]; exact hc.kept.sl
  refine pdCall c hok fun s' hrd hwr hsp hf hcs hvs hpost => ?_
  have hpw : Proof.RsaPkcs1Sig.AArch64.pubWr t = [⟨L.out, L.k.toNat⟩, L.SCR] := by
    simp only [Proof.RsaPkcs1Sig.AArch64.pubWr, h.x0, h.x1, a0, a1, olk]
  rw [hpw] at hf
  have hlow : Region.Sub (below t.sp (16 * c.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega_arith)
  have hws : ∀ r ∈ ([⟨L.out, L.k.toNat⟩, L.SCR] : List Region) ++ [below t.sp (16 * c.code.aarch64Depth)],
      (Region.Sub r L.OUT ∨ Region.Sub r L.SCR) ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (.inl fun _ h => h)
    · exact .inl (.inr fun _ h => h)
    · exact .inr hlow
  have hkept : ∀ d, keptOff d → ∀ R ∈ ([⟨L.out, L.k.toNat⟩, L.SCR] : List Region) ++
      [below t.sp (16 * c.code.aarch64Depth)], Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun d hd R hR => by
    rcases hws R hR with hs | hs
    · exact hL.kept_buf hd hs
    · exact (hL.fr_low (by unfold keptOff at hd; omega_arith)).sub_right hs
  have hzr : ∀ R ∈ ([⟨L.out, L.k.toNat⟩, L.SCR] : List Region) ++ [below t.sp (16 * c.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 oZ, 8⟩ R := fun R hR => by
    rcases hws R hR with hs | hs
    · rcases hs with hs | hs
      · exact (hL.stk_buf (by decide) (.inl rfl)).sub_right hs
      · exact (hL.stk_buf (by decide) (.inr (.inr (.inr (.inr (.inr rfl)))))).sub_right hs
    · exact (hL.fr_low (by decide)).sub_right hs
  refine ⟨⟨⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30), fun r hr => (hvs r hr).trans (hc.vs r hr),
    hc.kept.frame hf hkept, hc.frame.trans (hf.sub fun r hr => ?_)⟩, ?_⟩, fun hq => ?_⟩
  · rcases hws r hr with (hs | hs) | hs
    · exact ⟨L.OUT, by simp, hs⟩
    · exact ⟨L.SCR, by simp, hs⟩
    · exact ⟨L.STK, by simp, fun x hx => (Lay.Ok.low_stk (L := L)) x (hs x hx)⟩
  · rw [hf.readW (Region.contains_self _ _) hzr (by decide)]; exact h.z
  · rw [h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, olk, h.em, pre_words hL hc h.pre,
      bytesAt_eq (n := L.el.toNat) (fun i hi => hc.byte_ro (R := L.E) hL.oE.symm hL.eS hL.kE.symm
        (Nat.le_of_lt L.el.isLt) hi)] at hpost
    exact hpost _ (by simp [Spec.Rsa.bytesAt]) hq

end VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc
