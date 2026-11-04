module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptData
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Core
import VerifiedGarbage.Proof.Bignum.Math

/-! # FFDH key generation from the context on x86-64: the attempt

`vg_ffdh_generate_key`'s attempt with the scalar cut at the context's width
(`metaLoad`) and `g^x mod p` by the context's comb (`comb_ok`). -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached (at_)
open VG.Impl.Ffdh.X86_64.Cached.Generate (metaLoad)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey

theorem ofInt_zero' (b : Addr) : b + BitVec.ofInt 64 0 = off b 0 := rfl
theorem ofInt_eight (b : Addr) : b + BitVec.ofInt 64 8 = off b 8 := rfl

theorem toNat_mod64 {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat % 64 = x % 64 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- The context's width: `sEl :=` its bytes, `sMsk :=` the mask of its first byte. -/
theorem metaLoad_inputs {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Inputs p rb s)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params)) :
    WP isa (.block metaLoad) s fun t =>
      Inputs p rb t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧
      word t.mem p.B (8 * sMsk) = p.msk ∧ Frm p.B scanRanges s.mem t.mem ∧
      Keep [.rax, .rsi, .rdx, .rcx] s t := by
  have hZ := h.base.hZ
  have hk := h.base.k2
  obtain ⟨hw0, hw1, _⟩ := hc.hdr
  have hr0 : InRegions (s.rd ++ s.wr) cp 8 := by simpa [off] using hc.reg.rd 0 (by omega)
  have hw0' : s.mem.readW cp 64 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) := by
    simpa [Bignum.word, off] using hw0
  have hr1 : InRegions (s.rd ++ s.wr) (off cp 8) 8 := hc.reg.rd 1 (by omega)
  have hn : p.n = (Spec.Ffdh.generationScalarBits p.params + 7) / 8 := by
    change p.k - p.ld = _; rw [hld]; omega
  have hsub : BitVec.ofNat 64 (8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8)) -
      BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits p.params) =
      BitVec.ofNat 64 (8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) - Spec.Ffdh.generationScalarBits p.params) :=
    sub_ofNat (by omega) (by omega)
  let m := (s.mem.writeW (off p.B (8 * sEl)) (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8))).writeW
    (off p.B (8 * sMsk)) (cgMask (Spec.Ffdh.generationScalarBits p.params))
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx] (Q := fun t => t.mem = m) (by
    unfold metaLoad
    xrun [State.ea, VG.Impl.Rsa.X86_64.Crt.stk, hdr, at_, h.rdi, hsp, hdrOff, hc.sprd, hc.sp, atOff', hr0, hr1,
      hw0', hw1, h.base.scr.st (d := 8 * sEl) (by change 200 ≤ p.Z; omega),
      h.base.scr.st (d := 8 * sMsk) (by change 256 ≤ p.Z; omega), shl3 (show 8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) < 2 ^ 64 by omega),
      hsub, execShiftCl, VarShiftOp.eval, toNat_mod64 (show 8 * ((Spec.Ffdh.generationScalarBits p.params + 7) / 8) -
        Spec.Ffdh.generationScalarBits p.params < 2 ^ 64 by omega), m, cgMask]
    rfl) rfl)
    fun t ⟨hm, k⟩ => ?_
  have o1 := writeW_outside s.mem p.B (d := 8 * sEl)
    (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8)) (by decide)
  have o2 := writeW_outside (s.mem.writeW (off p.B (8 * sEl))
    (BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits p.params + 7) / 8))) p.B (d := 8 * sMsk)
    (cgMask (Spec.Ffdh.generationScalarBits p.params)) (by decide)
  have hf : Frm p.B scanRanges s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside o1 (by simp [scanRanges])).trans (Frm.of_outside o2 (by simp [scanRanges]))
  refine ⟨h.keep hf k (by decide), ?_, ?_, hf, k⟩
  · rw [hm, o2.word (by decide) (by decide), word_writeW_self, hn]
  · rw [hm, word_writeW_self, hmsk]

/-- The sampled scalar is ready for the existing private-key arithmetic proofs. -/
def ScalarPostC (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  CheckPrivate.Base p.kp (p.xb rb) t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ t.gpr .rdi = p.B ∧
    word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep mmRegs s t

/-- The sampled scalar, cut at the context's width. -/
theorem scalarC_ok {p : GkP} {rb : List Byte} {s : State} {cp : Addr} (h : Inputs p rb s)
    (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp) (hm : p.mv = true)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8 * p.k)
    (hld : p.ld = p.k - (Spec.Ffdh.generationScalarBits p.params + 7) / 8)
    (hmsk : p.msk = cgMask (Spec.Ffdh.generationScalarBits p.params)) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Cached.Generate.scalar) s fun t => ScalarPostC p rb s t ∧ CtxIn p cp t := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.scalar
  change WP isa (.seq (.block metaLoad) (.seq (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutSetup)
    (.seq (.loop (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutBody) .ne)
      (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.cutFinish)))) s _
  refine WP.seq (WP.mono (metaLoad_inputs h hc hsp h1 h8 hld hmsk) fun v ⟨hv, hnv, hmask, hfv, k₂⟩ => ?_)
  refine WP.seq (WP.mono (cutSetup_ok hv hnv hmask) fun z ⟨⟨hr, hmz⟩, k₃⟩ => ?_)
  have hz : Inputs p rb z := hv.keep (by intro a _; rw [hmz]) k₃ (by decide)
  refine WP.seq (WP.mono (cut_inputs hz hr) fun a ⟨ha, hx, hh, h8', hf₄, k₄⟩ => ?_)
  have hna : word a.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := ha.base.hZ; change 200 ≤ p.Z; omega), hmz]
    exact hnv
  refine WP.mono (finish_base ha hx hm hna h8') fun t ⟨hb, hd, hG, hQ, hs, hi, k₅⟩ => ?_
  have hZ : 256 ≤ p.Z := by have := h.base.hZ; omega
  have f₁ : RunFrame p s.mem v.mem := .of_frm hfv (fun r hr => Nat.le_trans (scanRanges_end r hr) hZ)
  have f₃ : RunFrame p v.mem z.mem := by rw [hmz]; exact .refl _ _
  have F : RunFrame p s.mem t.mem := ((f₁.trans f₃).trans hf₄).trans (.of_scr hi)
  have K := ((k₂.trans k₃).trans (k₄.trans k₅))
  refine ⟨⟨hb, hx.congrK hi k₅, hd, hG, hQ, ?_, F, K.mono (by decide)⟩, hc.keep F K.2.1 K.2.2⟩
  intro i hi'
  have sv : word v.mem p.B (8 * i) = word s.mem p.B (8 * i) := hfv.word_eq (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega) (by omega)
  rw [hs i hi', hh _ (by have := h.base.hZ; omega), hmz, sv]

/-- `g^x mod p` by the context's comb, from `R² mod p`. -/
theorem ready_comb (Mo : Mont) {p : GkP} {rb : List Byte} {cp : Addr} {s : State}
    (h : CheckPrivate.Ready p.kp (p.xb rb) s) (hc : CtxIn p cp s) (hsp : s.gpr .rsp = p.sp)
    (h1 : 1 ≤ Spec.Ffdh.generationScalarBits p.params) (h8 : Spec.Ffdh.generationScalarBits p.params ≤ 8192)
    (hxb : Spec.Rsa.os2ip (p.xb rb) < 2 ^ Spec.Ffdh.generationScalarBits p.params) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Cached.Generate.comb Mo.mm)) s
      (CheckPrivate.StepPost p.kp s (CheckPrivate.Value p.kp (p.xb rb))) := by
  obtain ⟨mi, hb, hcm, hG⟩ := h
  have hk := hb.k2
  have hrs := Rsa.FixedBaseComb.rows_small h8
  have hrp := Rsa.FixedBaseComb.rows_pos (show 0 < Spec.Ffdh.generationScalarBits p.params by omega)
  have hxl : (p.xb rb).length = p.kp.xl := hb.xlen
  have hxk : p.kp.xl ≤ p.kp.k := hb.xl2
  refine WP.mono (comb_ok Mo (T := cgT p mi cp) hcm (by rw [hsp]; exact hc.sprd)
    (fun hm => by rw [hsp]; exact hc.sp_inScr hm) (by rw [hsp]; exact hc.sp)
    (hb.hdr (sX, p.kp.xp) (by simp [CheckPrivate.KpP.headers]))
    (by rw [hxl]; exact hb.hdr (sXl, BitVec.ofNat 64 p.kp.xl) (by simp [CheckPrivate.KpP.headers]))
    hc.reg hc.hdr.2.2 (hc.ent mi) hb.x hrp
    (show 5 * Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits p.params) < 2 ^ 31 by omega) (by rw [hxl]; change 8 * p.kp.xl < 2 ^ 32; omega) hxb)
    fun t ⟨hct, hy, hf, k⟩ => ?_
  have hr : ∀ r ∈ innerR p.w, r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 :=
    fun r hr => by have := (innerR_ok p.w r hr).2.1; omega
  obtain ⟨hb', hi, hs⟩ := hb.child hcm.sub hf hr k
  obtain ⟨hh, _⟩ := VG.Proof.Ffdh.X86_64.child_frm hcm.sub hcm.wide hf hr
  refine ⟨⟨⟨mi, hb', hct, (hh _ (by decide)).trans hG⟩, hy.trans ?_⟩, hi, hs, k.mono (by decide)⟩
  rw [powMod_eq]
  rfl

end VG.Proof.Ffdh.X86_64.Cached
