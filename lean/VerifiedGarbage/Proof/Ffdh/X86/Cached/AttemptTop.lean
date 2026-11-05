module

public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.MetaCut
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Framework.CallLay

/-! # `vg_ffdh_generate_key_cached` on i686 against its contract -/

@[expose] public section

/-!
# FFDH key generation from the context on i686: the attempt's body

`body_ok`: `vg_ffdh_generate_key`'s body with the cut at the context's
public width (`metaCut`, by `KeyGen.prefixWith_ok`) and y by the context's
comb (`comb`, by `KeyGen.tailWith_ok`), for a valid domain and its context.
-/

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.KeyGen
open VG.Impl.Ffdh.X86 VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate

/-- The context's public words and entries, for the width `bits`, p `P` and g `G`. -/
structure CtxVals (len : Nat) (args : Nat → BitVec 32) (P G bits : Nat) (m : Mem) : Prop where
  w0 : w32 m (ctxAddr args) 0 = bits
  w8 : w32 m (ctxAddr args) 8 = (bits + 7) / 8
  w16 : w32 m (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits
  ents : ∀ e < 32, val32 m (ctxAddr args) (24 + bc len .wide * (2 + e)) (cwc len .wide) =
    Spec.Rsa.powMod G (Spec.Rsa.FixedBaseComb.exponent bits e) P * 2 ^ (8 * bc len .wide) % P

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The context's values through writes apart from it. -/
theorem CtxVals.keep {P G bits : Nat} {m m' : Mem} (V : CtxVals len args P G bits m) {rs : List Region}
    (F : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ r)
    (hn : ctxBytes len < 2 ^ 64) : CtxVals len args P G bits m' := by
  have bw := bc_eq_cwc len .wide
  have far : ∀ {d N : Nat}, d + 4 * N ≤ ctxBytes len → val32 m' (ctxAddr args) d N = val32 m (ctxAddr args) d N :=
    fun {d N} h => val32_far F (fun r hr => (hd r hr).sub_left (Offset.sub_base _ h)) (by omega)
  have w : ∀ {d : Nat}, d + 4 ≤ ctxBytes len → w32 m' (ctxAddr args) d = w32 m (ctxAddr args) d := fun {d} h => by
    rw [← w32_val32_one, ← w32_val32_one]; exact far (by omega)
  refine ⟨by rw [w (by simp only [ctxBytes]; omega)]; exact V.w0, by rw [w (by simp only [ctxBytes]; omega)]; exact V.w8,
    by rw [w (by simp only [ctxBytes]; omega)]; exact V.w16, fun e he => ?_⟩
  have : bc len .wide * (2 + e) + bc len .wide ≤ bc len .wide * 34 := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  rw [far (by simp only [ctxBytes]; omega)]; exact V.ents e he

/-- The context is apart from the working space's frame. -/
theorem ctx_frameR (C : CtxRd base bytes len args s) {sp : BitVec 32}
    (hstk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below sp 96)) {ws : List (Nat × Nat)}
    (hws : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    ∀ r ∈ frameR base sp ws, Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ r := by
  intro r hr
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact hstk
  · exact C.apart.sub_right (Offset.sub_base _ (hws p hp))

/-- The comb as a stage computing y into slot 6. -/
theorem combStage_ok (h : In Ex base bytes len args s) {P G x bits : Nat}
    (E : CombEnv Ex base bytes len args P G x bits s)
    (hP : safeM (sv s.mem base len .wide 9) = P) (hx : x < 2 ^ bits) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hrows : w32 s.mem (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa Generate.comb s fun u => Step Ex base bytes len args s u ∧
      Kept base len [] [rowsOff, iOff] s.mem u.mem ∧ sv u.mem base len .wide 6 = Spec.Rsa.powMod G x P := by
  refine WP.mono (comb_ok h E hP hx hR hrows) fun u ⟨C, Y, _, F, K⟩ => ?_
  have inF : ∀ p ∈ combR len, InF len p := by
    have hs := stR_inF h
    have nb : numBase = 3336 := rfl
    have hn := h.need
    have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
    intro p hp
    simp only [combR, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact .inr ⟨by simp only [rowsOff]; omega, by simp only [rowsOff]; omega⟩
    · exact .inr ⟨by simp only [iOff]; omega, by simp only [iOff]; omega⟩
    · exact hs p (by simpa only [stR, List.mem_cons, List.not_mem_nil, or_false] using hp)
  refine ⟨⟨C.inp, fR_widen F inF, K⟩, ⟨fun j a b _ => combR_sv h F h.room a b, fun d a b c hd => ?_⟩, Y⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  exact combR_w32 h F h.room a b c hd.1 hd.2

end

/-! ## The body -/

/-- What the contract asks of the status and the outputs. -/
def CachedKeyPost (len dlen : Nat) (m : Mem) (args : Nat → BitVec 32) (r : Nat) (m' : Mem) : Prop :=
  let a := CheckPrivate.params m args len dlen
  let x := Spec.Ffdh.vettedScalarOfOctets a (Spec.Rsa.bytesAt m (byteAddr (args 10)) len)
  r = Spec.Ffdh.keyStatus a x ∧
    if Spec.Ffdh.keyStatus a x = 1 then
      Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = Spec.Rsa.i2osp x len ∧
        Spec.Rsa.bytesAt m' (byteAddr (args 8)) len = Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) len
    else Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = List.replicate len 0 ∧
      Spec.Rsa.bytesAt m' (byteAddr (args 8)) len = List.replicate len 0

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The width's cut of `rand` is the vetted scalar. -/
theorem cut_vetted {m : Mem} {bits : Nat} (hb : bits ≤ 8 * len) (hl : 0 < len) :
    cutOf m args len (len - VG.Proof.Ffdh.ScalarWidth.width bits) (VG.Proof.Ffdh.ScalarWidth.mask bits) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 10)) len) % 2 ^ bits := by
  have := VG.Proof.Ffdh.ScalarWidth.cut_value (r := Spec.Rsa.bytesAt m (byteAddr (args 10)) len) (bits := bits)
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hl) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hb)
  rw [VG.Proof.Bignum.bytesAt_length] at this
  exact this

theorem body_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (C : KeyCut.CutGeo base bytes len (args 10) (args 0) (s.gpr .esp) s.rd s.wr)
    (rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩)
    (r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below (s.gpr .esp) 96))
    (domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (Oy : OutAt args base bytes len 8 (s.gpr .esp) s.wr)
    (h9a : args 9 = BitVec.ofNat 32 len) (xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩)
    (CR : CtxRd base bytes len args s)
    (cstk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below (s.gpr .esp) 96))
    (cx : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨byteAddr (args 0), len⟩)
    (dv : Spec.Ffdh.domainValid len (domOf s.mem args dlen) = true)
    (CV : CtxVals len args (comp s.mem args len 0) (comp s.mem args len 1)
      (Spec.Ffdh.generationScalarBits (CheckPrivate.params s.mem args len dlen)) s.mem) :
    WP isa Generate.body s fun t => ∃ r, t.gpr .eax = BitVec.ofNat 32 r ∧
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ CachedKeyPost len dlen s.mem args r t.mem := by
  have fit := G.fit
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have h2 : 2 * len ≤ dlen := by omega_arith
  have hn : ctxBytes len < 2 ^ 64 := by
    have := CR.afit; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega
  -- The width.
  generalize hbits : Spec.Ffdh.generationScalarBits (CheckPrivate.params s.mem args len dlen) = bits at CV
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  have hb1 : 1 ≤ bits := by rw [← hbits]; exact bf.1
  have hb : bits ≤ 8 * len := by rw [← hbits]; exact bf.2
  have sm := (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := bits) (by omega_arith)).1
  have hR := VG.Proof.Rsa.FixedBaseComb.rows_pos (bits := bits) (by omega_arith)
  unfold Generate.body
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
    (h.arg (i := 3) (by decide))) fun u ⟨P, Cc, M, K⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u := Step.regs h M K
  have rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
    rw [P, K.2.1, K.2.2]
    have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  refine WP.seq (WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega_arith) rd (by rw [Cc, G.e3]))
    fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have e0 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) = comp s.mem args len 0 :=
    CheckDomain.argNum_comp s.mem args len
  rw [e0] at Z
  have S := S₁.trans (Step.regs S₁.inp Mv Kv)
  have Mvs : v.mem = s.mem := Mv.trans M
  -- The valid domain's modulus is valid.
  have mv : Spec.Rsa.modulusValid (comp s.mem args len 0) len = true := by
    have := VG.Proof.Ffdh.domainValid_mod dv
    rwa [← comp_p s.mem args h2] at this
  refine WP.ite _ Z (fun _ => ?_) (fun invalid => absurd mv (by rw [invalid]; decide))
  have sp : v.gpr .esp = s.gpr .esp := S.esp
  have G' := G.keep ⟨rfl, rfl⟩ S.keeps
  have Cv : KeyCut.CutGeo base bytes len (args 10) (args 0) (v.gpr .esp) v.rd v.wr := by
    rw [sp, S.keeps.2.1, S.keeps.2.2]; exact C
  have CVv : CtxVals len args (comp s.mem args len 0) (comp s.mem args len 1) bits v.mem := by rw [Mvs]; exact CV
  have wlt : len - VG.Proof.Ffdh.ScalarWidth.width bits < len := by
    have := VG.Proof.Ffdh.ScalarWidth.width_pos bits; omega_arith
  -- The front, with the cut at the context's width.
  have front := frontWith_ok G' (prefixWith_ok S.inp G' (by rw [sp]; exact hb40) Cv rWs (by rw [sp]; exact r40) domX
    wlt fun w Sw => by
      have CVw := CVv.keep Sw.frame (ctx_frameR CR (by rw [sp]; exact cstk) (fR_fit S.inp)) hn
      refine WP.mono (metaCut_ok Sw.inp (CR.keep (S.keeps.trans Sw.keeps)) G.e3 hb1 hb CVw.w0 CVw.w8)
        fun t ⟨St, k, ld, tt⟩ => ⟨St, k.mono, ld, tt⟩)
  rw [show Generate.main = Prog.chain (mainFrontWith Generate.metaCut)
    (.ite .e GenerateKey.fail (tailWith Generate.comb)) from rfl]
  refine WP.chain_split front fun u F => ?_
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := S.keeps.trans F.keeps
  have spu : u.gpr .esp = s.gpr .esp := by rw [F.keeps.1 _ (by decide), sp]
  have Ox' : OutAt args base bytes len 0 (u.gpr .esp) u.wr := by rw [spu]; exact Ox.keep rfl Ku
  have Oy' : OutAt args base bytes len 8 (u.gpr .esp) u.wr := by rw [spu]; exact Oy.keep rfl Ku
  have FF : ∀ {t : State}, Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ ::
      frameR base (u.gpr .esp) (fR len)) u.mem t.mem →
      Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr (args 8), len⟩ :: frameR base (s.gpr .esp) (fR len))
        s.mem t.mem := fun {t} Ft => by
    have Fv := F.frame
    have Fs := S.frame
    rw [sp] at Fv
    rw [spu] at Ft
    refine ((Fs.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans
      (Fv.mono fun r hr => ?_)).trans Ft
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  have pv0 : Spec.Ffdh.parametersValid (CheckPrivate.params s.mem args len dlen) = true := by
    have e := dv
    unfold Spec.Ffdh.domainValid at e
    simp only [Bool.and_eq_true] at e
    exact e.1
  have vs : Spec.Ffdh.vettedScalarOfOctets (CheckPrivate.params s.mem args len dlen)
      (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) % 2 ^ bits := by
    rw [← hbits]; rfl
  have gate := F.gate
  rw [Mvs, cut_vetted hb (by omega_arith)] at gate
  refine WP.gate gate (fun inval => WP.mono (fail_ok F.inp Ox' Oy' h9a xy) fun t ⟨E, Bx, By, Ft, Kt⟩ =>
    ⟨2, E, FF Ft, Ku.trans Kt, ?_⟩) (fun val => ?_)
  · have ks : Spec.Ffdh.keyStatus (CheckPrivate.params s.mem args len dlen)
        (Spec.Ffdh.vettedScalarOfOctets (CheckPrivate.params s.mem args len dlen)
          (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len)) = 2 := by
      rw [vs]; unfold Spec.Ffdh.keyStatus; rw [inval]; rfl
    refine ⟨ks.symm, ?_⟩
    simp only [ks]
    exact ⟨Bx, By⟩
  · have v9 := F.v9
    have v10 := F.v10
    have v13 := F.v13
    have v15 := F.v15
    have v16 := F.v16
    rw [Mvs] at v9 v10 v15 v16
    rw [Mvs, cut_vetted hb (by omega_arith)] at v13
    generalize hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 10)) len) % 2 ^ bits = x at v13 val vs
    have xb : x < 2 ^ bits := by rw [← hx]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have xlt : x < 2 ^ (8 * len) := Nat.lt_of_lt_of_le xb (Nat.pow_le_pow_right (by decide) hb)
    have mv' := mv
    unfold Spec.Rsa.modulusValid at mv'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv'
    have p1 : 1 < comp s.mem args len 0 := by have := Nat.two_pow_pos 511; have := mv'.1.1.2; omega_arith
    have sP : safeM (comp s.mem args len 0) = comp s.mem args len 0 := safeM_of p1 mv'.1.1.1
    have Plt : comp s.mem args len 0 < 2 ^ (8 * len) := comp_lt s.mem 0
    have ylt : Spec.Rsa.powMod (comp s.mem args len 1) x (comp s.mem args len 0) < 2 ^ (8 * len) := by
      rw [VG.Proof.Bignum.powMod_eq]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) Plt
    have CVu : CtxVals len args (comp s.mem args len 0) (comp s.mem args len 1) bits u.mem := by
      have Fv := F.frame
      rw [sp, Mvs] at Fv
      have Fu := Fv
      refine CV.keep Fu (fun r hr => ?_) hn
      rcases List.mem_cons.mp hr with rfl | hr
      · exact cx
      · exact ctx_frameR CR cstk (fR_fit h) r hr
    have E : CombEnv Ex base bytes len args (comp s.mem args len 0) (comp s.mem args len 1) x bits u :=
      ⟨CR.keep Ku, by rw [spu]; exact cstk, CVu.ents, v13, sm⟩
    refine WP.mono (tailWith_ok (G.keep ⟨rfl, rfl⟩ Ku) Ox' Oy' h9a xy v9 sP v13 F.v14 v15 v16 xlt ylt
      (combStage_ok F.inp E (by rw [v9, sP]) xb hR CVu.w16)) fun t ⟨E', Bx, By, Ft, Kt⟩ =>
      ⟨_, E', FF Ft, Ku.trans Kt, ?_⟩
    dsimp only [CachedKeyPost]
    have hpa := comp_p s.mem args h2
    have hga := comp_g s.mem args h2
    have hqa : (CheckPrivate.params s.mem args len dlen).q =
        if dlen = 2 * len then none else some (comp s.mem args len 2) := by
      rcases dl with e | e
      · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_arith)
      · have : ¬ 3 * len = 2 * len := by omega_arith
        simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
    have pv : Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) x = true := by
      cases c : Spec.Ffdh.privateValid (CheckPrivate.params s.mem args len dlen) x
      · exact absurd c val
      · rfl
    rw [vs]
    rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq pv0, pv]
    simp only [VG.Proof.Bignum.powMod_eq] at E' Bx By ⊢
    have ai := accept_iff (len := len) (dlen := dlen) (y := comp s.mem args len 1 ^ x % comp s.mem args len 0)
      hpa.symm p1 hqa
    rw [show (CheckPrivate.params s.mem args len dlen).g = comp s.mem args len 1 from hga.symm,
      show (CheckPrivate.params s.mem args len dlen).p = comp s.mem args len 0 from hpa.symm]
    simp only [Bool.true_eq_false, ↓reduceIte]
    by_cases hc : accept len dlen (comp s.mem args len 0) (comp s.mem args len 2) (comp s.mem args len 0)
      (comp s.mem args len 1 ^ x % comp s.mem args len 0) = true
    · rw [hc] at E' Bx By ⊢
      rw [ai.mp hc]
      simp only [↓reduceIte] at E' Bx By ⊢
      exact ⟨trivial, Bx, By⟩
    · have hc' : accept len dlen (comp s.mem args len 0) (comp s.mem args len 2) (comp s.mem args len 0)
          (comp s.mem args len 1 ^ x % comp s.mem args len 0) = false := by simpa using hc
      have hv : Spec.Ffdh.publicValid ⟨CheckPrivate.params s.mem args len dlen,
          comp s.mem args len 1 ^ x % comp s.mem args len 0⟩ = false := by
        cases c : Spec.Ffdh.publicValid ⟨CheckPrivate.params s.mem args len dlen,
          comp s.mem args len 1 ^ x % comp s.mem args len 0⟩
        · rfl
        · exact absurd (ai.mpr c) hc
      rw [hc'] at E' Bx By ⊢
      rw [hv]
      simp only [Bool.false_eq_true, ↓reduceIte] at E' Bx By ⊢
      exact ⟨trivial, by rw [Bx]; exact VG.Proof.Bignum.i2osp_zero' _, by rw [By]; exact VG.Proof.Bignum.i2osp_zero' _⟩

end

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In safeM safeM_of bc cwc mw)
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)
open VG.Impl.Ffdh.X86.Cached

/-! ## The context's values -/

/-- The context's words give its public words and entries. -/
theorem ctxVals_of {m : Mem} {args : Nat → BitVec 32} {len : Nat} {dom : List Byte}
    (h : Spec.Rsa.wordsAt m (ctxAddr args) (3 + 34 * mw len) = generationValues len dom)
    (dv : Spec.Ffdh.domainValid len dom = true) (hl : len ≤ 1024) (hp : 0 < (Spec.Ffdh.domainOf len dom).p)
    (hpl : (Spec.Ffdh.domainOf len dom).p < 2 ^ (8 * len)) :
    CtxVals len args (Spec.Ffdh.domainOf len dom).p (Spec.Ffdh.domainOf len dom).g
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom)) m := by
  obtain ⟨e0, e8, e16, _, _, ee⟩ := VG.Proof.Ffdh.ContextRows.ctx_of_values h
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  generalize Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) = bits at bf e0 e8 e16 ee ⊢
  generalize (Spec.Ffdh.domainOf len dom).p = P at hp hpl ee ⊢
  have b32 : bits < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_trans bf.2 (Nat.mul_le_mul_left 8 hl)) (by decide)
  have b64 : (2 : Nat) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
  have rs := (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := bits) (by omega)).1
  have small : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 64 v).toNat % 2 ^ 32 = v := fun {v} hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv b64), Nat.mod_eq_of_lt hv]
  have hb : bc len .wide = 8 * mw len := rfl
  have hc : cwc len .wide = 2 * mw len := by simp only [cwc, hb]; omega
  have hpw : 2 ^ (8 * len) ≤ 2 ^ (64 * mw len) :=
    Nat.pow_le_pow_right (by decide) (by simp only [mw, Spec.Rsa.modulusWords]; omega)
  refine ⟨?_, ?_, ?_, fun e he => ?_⟩
  · rw [VG.Proof.Ffdh.ContextRows.w32_of_word, e0, small b32]
  · rw [VG.Proof.Ffdh.ContextRows.w32_of_word, e8, small (by omega)]
  · rw [VG.Proof.Ffdh.ContextRows.w32_of_word, e16, small (by omega)]
  · rw [hc, VG.Proof.Ffdh.ContextRows.val32_eq_wv, hb, show 8 * (8 * mw len) = 64 * mw len by omega]
    exact VG.Proof.Ffdh.ContextRows.value_of_row (ee e he)
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (Nat.le_of_lt hpl)) hpw)

/-! ## The ABI -/

/-- What the contract gives `vg_ffdh_generate_key_cached(x, x_len, y, y_len, domain, domain_len, p_len,
rand, rand_len, scratch, scratch_len, ctx, ctx_len)`. -/
structure CachedABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 52 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩,
    ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩, ⟨argAddr s 0, 52⟩]
  xy : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  xDom : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  xRand : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  xScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  xCtx : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  xArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  yDom : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  yRand : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  yScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  yCtx : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  yArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  domScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  domArgs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  randScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  randArgs : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  scratchCtx : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  ctxArgs : (⟨argumentPointer s 11, (arg s 12).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  retX : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retY : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  retDom : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  retCtx : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowY : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  belowRand : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowCtx : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  xBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  domBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  randBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  ctxBound : (arg s 11).toNat + (arg s 12).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 6).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 6).toNat (arg s 5).toNat
  xLen : (arg s 1).toNat = (arg s 6).toNat
  yLen : (arg s 3).toNat = (arg s 6).toNat
  randLen : (arg s 8).toNat = (arg s 6).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 6).toNat ≤ (arg s 10).toNat
  valid : Spec.Ffdh.domainValid (arg s 6).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat) = true
  ctxLen : (arg s 12).toNat = Spec.Ffdh.generationPrecomputedWords (arg s 6).toNat
  ctx : Spec.Ffdh.generationPrecompute (arg s 6).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat) =
    some (Spec.Rsa.wordsAt s.mem (argumentPointer s 11) (arg s 12).toNat)

theorem cachedABI_of {s : State} (h : (Spec.Ffdh.cachedGenerateKeyContract abi stack).pre s) : CachedABI s := by
  sig_pre [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

abbrev gArgs : Impl.Ffdh.X86.Args := Impl.Ffdh.X86.Cached.Generate.args

theorem wrapABI {s : State} (A : CachedABI s) : WrapABI gArgs 13 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h; decide), by decide, (fun _ h => by cases h; decide)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by
    rw [A.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill gArgs)) Impl.Ffdh.X86.Cached.Generate.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The bytes of the domain and of `rand` at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat
abbrev entryRand (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat

/-- The context. -/
abbrev ctxR (s : State) : Region := ⟨argumentPointer s 11, (arg s 12).toNat * 8⟩

/-- What the body may read: the domain, `rand` and the context; and write: x and y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 4) (arg s 5).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 7) (arg s 8).toNat ∧
    InRegions wr (argumentPointer s 0) (arg s 1).toNat ∧ InRegions wr (argumentPointer s 2) (arg s 3).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 11) ((arg s 12).toNat * 8)

/-- The 96 bytes below the frame, and the frame, below the caller's stack pointer. -/
theorem frame_subs {s : State} (A : CachedABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) :
    Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ∧
      Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  refine ⟨?_, ?_⟩
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  · rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)

theorem frame_geo {s : State} (A : CachedABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    Geo (synth gArgs (arg s)) (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (arg s 5).toNat sp rd wr := by
  obtain ⟨sub40, subF⟩ := frame_subs A espf
  have xL : (arg s 1).toNat = pLenOf gArgs s := A.xLen
  have yL : (arg s 3).toNat = pLenOf gArgs s := A.yLen
  have rL : (arg s 8).toNat = pLenOf gArgs s := A.randLen
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have dx : Region.Disjoint ⟨argumentPointer s 0, pLenOf gArgs s⟩ ⟨argumentPointer s 2, pLenOf gArgs s⟩ := by
    have := A.xy; rw [xL, yL] at this; exact this
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, (A.belowDom.sub_left sub40).symm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, (ofn _).symm, dx⟩
  · show (arg s 7).toNat + _ ≤ _
    rw [← rL]; exact A.randBound
  · show (arg s 0).toNat + _ ≤ _
    rw [← xL]; exact A.xBound
  · show InRegions _ (argumentPointer s 7) _
    rw [← rL]; exact hrd.2.1
  · show InRegions _ (argumentPointer s 0) _
    rw [← xL]; exact hrd.2.2.1
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ ⟨argumentPointer s 0, _⟩
    have := A.xRand.symm; rw [rL, xL] at this; exact this
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← xL]; exact A.xScratch
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.belowX.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← rL]; exact A.randScratch
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← rL]; exact (A.belowRand.sub_left sub40).symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.xDom.symm
  · show (arg s 0).toNat + _ ≤ _
    rw [← xL]; exact A.xBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← xL]; exact hrd.2.2.1
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.xScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.belowX.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← xL]; exact (A.belowX.sub_left sub40).symm
  · show (arg s 2).toNat + _ ≤ _
    rw [← yL]; exact A.yBound
  · show InRegions _ (argumentPointer s 2) _
    rw [← yL]; exact hrd.2.2.2.1
  · show Region.Disjoint _ ⟨argumentPointer s 2, _⟩
    rw [← yL]; exact A.yScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 2, _⟩
    rw [← yL]; exact A.belowY.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 2, _⟩ _
    rw [← yL]; exact (A.belowY.sub_left sub40).symm

theorem genWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_far {s : State} (A : CachedABI s) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase gArgs s, wsSize gArgs s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) :
    ∀ r ∈ [(⟨wsBase gArgs s, wsSize gArgs s⟩ : Region), ⟨frameAt s, argsFrame⟩], Region.Disjoint ⟨p, n⟩ r := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hws
  · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm

theorem frame_keep {s : State} (A : CachedABI s) {m : Mem}
    (Ft : Frame [⟨wsBase gArgs s, wsSize gArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase gArgs s, wsSize gArgs s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n :=
  frame_bytes Ft (frame_far A hws hb) hn

/-- The context's bytes. -/
theorem ctxBytes_eq {s : State} (A : CachedABI s) : (arg s 12).toNat * 8 = ctxBytes (pLenOf gArgs s) := by
  have := A.ctxLen
  rw [genWords_eq] at this
  simp only [ctxBytes, bc, mw, Spec.Rsa.modulusWords]
  show _ = 24 + 8 * (((arg s 6).toNat + 7) / 8) * 34
  omega

/-- The context, as the body reads it. -/
theorem frame_ctx {s : State} (A : CachedABI s) {f : State} (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (hrd : Rd s f.rd f.wr) :
    CtxRd (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (synth gArgs (arg s)) f ∧
      Region.Disjoint ⟨ctxAddr (synth gArgs (arg s)), ctxBytes (pLenOf gArgs s)⟩ (below (f.gpr .esp) 96) ∧
      Region.Disjoint ⟨ctxAddr (synth gArgs (arg s)), ctxBytes (pLenOf gArgs s)⟩
        ⟨byteAddr (synth gArgs (arg s) 0), pLenOf gArgs s⟩ := by
  obtain ⟨sub40, _⟩ := frame_subs A espf
  have cb := ctxBytes_eq A
  have xL : (arg s 1).toNat = pLenOf gArgs s := A.xLen

  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · show InRegions _ (off (argumentPointer s 11) 0) _
    rw [← cb, show off (argumentPointer s 11) 0 = argumentPointer s 11 from BitVec.add_zero _]; exact hrd.2.2.2.2
  · show (argumentPointer s 11).toNat + 0 + ctxBytes (pLenOf gArgs s) ≤ 2 ^ 32
    rw [← cb]
    have := A.ctxBound
    have hv : (argumentPointer s 11).toNat = (arg s 11).toNat := by
      simp only [argumentPointer, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega)
    rw [hv]; omega
  · show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ _
    rw [← cb]; exact A.scratchCtx.symm
  · show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ _
    rw [← cb]; exact (A.belowCtx.sub_left sub40).symm
  · show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ ⟨argumentPointer s 0, _⟩
    rw [← cb, ← xL]; exact A.xCtx.symm

/-- What the contract asks of the status and the outputs. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  let a := Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)
  let x := Spec.Ffdh.vettedScalarOfOctets a (entryRand s)
  r.toNat = Spec.Ffdh.keyStatus a x ∧
    if Spec.Ffdh.keyStatus a x = 1 then
      Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 6).toNat = Spec.Rsa.i2osp x (arg s 6).toNat ∧
        Spec.Rsa.bytesAt m (argumentPointer s 2) (arg s 6).toNat =
          Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (arg s 6).toNat
    else Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 6).toNat = List.replicate (arg s 6).toNat 0 ∧
      Spec.Rsa.bytesAt m (argumentPointer s 2) (arg s 6).toNat = List.replicate (arg s 6).toNat 0

/-- The context's values at the frame's state. -/
theorem frame_vals {s : State} (A : CachedABI s) {m : Mem}
    (Ft : Frame [⟨wsBase gArgs s, wsSize gArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem m) :
    CtxVals (pLenOf gArgs s) (synth gArgs (arg s)) (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).p
      (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).g
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s))) m := by
  have dl : (arg s 5).toNat = 2 * (arg s 6).toNat ∨ (arg s 5).toNat = 3 * (arg s 6).toNat := A.dLen
  have lw := A.pLen.1
  have up := A.pLen.2
  have mv := VG.Proof.Ffdh.domainValid_mod A.valid
  have mv' := mv
  unfold Spec.Rsa.modulusValid at mv'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv'
  have hp : 0 < (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).p := by
    exact Nat.lt_of_lt_of_le (Nat.two_pow_pos 511) mv'.1.1.2
  have hpl : (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)).p < 2 ^ (8 * (arg s 6).toNat) := by
    have h1 := VG.Proof.Bignum.os2ip_lt ((entryDom s).take (arg s 6).toNat)
    have h2 : 256 ^ ((entryDom s).take (arg s 6).toNat).length ≤ 2 ^ (8 * (arg s 6).toNat) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega)
    change Spec.Rsa.os2ip ((entryDom s).take (arg s 6).toNat) < _
    omega
  have dlen : (arg s 6).toNat ≤ (entryDom s).length := by
    rw [VG.Proof.Bignum.bytesAt_length]; omega
  have W : Spec.Rsa.wordsAt s.mem (ctxAddr (synth gArgs (arg s))) (3 + 34 * mw (arg s 6).toNat) =
      generationValues (arg s 6).toNat (entryDom s) := by
    have c := A.ctx
    rw [VG.Proof.Ffdh.generationPrecompute_eq dlen mv, A.ctxLen, genWords_eq] at c
    exact (Option.some.inj c).symm
  have CV0 : CtxVals (pLenOf gArgs s) (synth gArgs (arg s)) _ _ _ s.mem := ctxVals_of W A.valid A.pLen.2 hp hpl
  have cb := ctxBytes_eq A
  have hn : ctxBytes (pLenOf gArgs s) < 2 ^ 64 := by
    have := A.ctxBound; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega
  exact CV0.keep Ft (frame_far A (by
    show Region.Disjoint ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩ _
    rw [← cb]; exact A.scratchCtx.symm)
    (by show Region.Disjoint _ ⟨argumentPointer s 11, ctxBytes (pLenOf gArgs s)⟩
        rw [← cb]; exact A.belowCtx)) hn

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CachedABI s) (f : State)
    (I : In (Rd s) (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (synth gArgs (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase gArgs s, wsSize gArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.Cached.Generate.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([xR s, yR s] ++ CrtRt.frameR (wsBase gArgs s) (f.gpr .esp) (fR (pLenOf gArgs s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  have Gm := frame_geo A espf I.extra
  obtain ⟨CR, cstk, cx⟩ := frame_ctx A espf I.extra
  have xL : (arg s 1).toNat = pLenOf gArgs s := A.xLen
  have yL : (arg s 3).toNat = pLenOf gArgs s := A.yLen
  have rL : (arg s 8).toNat = pLenOf gArgs s := A.randLen
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have D : Spec.Rsa.bytesAt f.mem (byteAddr (synth gArgs (arg s) 2)) (arg s 5).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega)
  have R : Spec.Rsa.bytesAt f.mem (byteAddr (synth gArgs (arg s) 10)) (pLenOf gArgs s) = entryRand s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _ = _
    rw [← rL]
    exact frame_keep A Ft A.randScratch A.belowRand (by have := A.randBound; omega)
  have pl : pLenOf gArgs s = (arg s 6).toNat := rfl
  have dl := Gm.dom.dl
  have lw := Gm.dom.lower
  have up := Gm.dom.upper
  have h2 : 2 * pLenOf gArgs s ≤ (arg s 5).toNat := by omega
  have dv : Spec.Ffdh.domainValid (pLenOf gArgs s) (domOf f.mem (synth gArgs (arg s)) (arg s 5).toNat) = true := by
    rw [domOf, D]; exact A.valid
  have CVf := frame_vals A Ft
  have CV : CtxVals (pLenOf gArgs s) (synth gArgs (arg s)) (comp f.mem (synth gArgs (arg s)) (pLenOf gArgs s) 0)
      (comp f.mem (synth gArgs (arg s)) (pLenOf gArgs s) 1)
      (Spec.Ffdh.generationScalarBits (CheckPrivate.params f.mem (synth gArgs (arg s)) (pLenOf gArgs s)
        (arg s 5).toNat)) f.mem := by
    rw [comp_p f.mem _ h2, comp_g f.mem _ h2]
    simp only [CheckPrivate.params, CheckDomain.domBytes]
    rw [D]; exact CVf
  refine WP.mono (body_ok I Gm.dom Gm.dom40 Gm.cut Gm.rWs Gm.r40 Gm.domX Gm.ox Gm.oy Gm.e9 Gm.xy CR cstk cx dv CV)
    fun t ⟨r, E, F, K, P⟩ => ⟨?_, ?_, K⟩
  · simp only [CachedKeyPost, CheckPrivate.params, CheckDomain.domBytes] at P
    rw [D, R] at P
    obtain ⟨hr, hb⟩ := P
    refine ⟨?_, hb⟩
    rw [E, BitVec.toNat_ofNat, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (keyStatus_le _ _) (by decide))
  · rw [List.cons_append, List.singleton_append, xR, yR, xL, yL]; exact F

theorem operation_ok {s : State} (A : CachedABI s) :
    WP isa Impl.Ffdh.X86.Cached.Generate.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _ ∧ InRegions _ _ _ ∧
      InRegions (s.rd ++ _) _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [xR s, yR s])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.retX
      · exact A.retY)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.xScratch.symm
      · exact A.yScratch.symm)
    (P := fun m e => spec s m e) fun f I espf Ft => frame_ok A f I espf Ft

theorem correct (s : State) (h : (Spec.Ffdh.cachedGenerateKeyContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Cached.Generate.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.cachedGenerateKeyContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (cachedABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Ffdh.X86.Cached
