module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.MetaCut
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH key generation from the context on i686: the attempt's body

`body_ok`: `vg_ffdh_generate_key`'s body with the cut at the context's
public width (`metaCut`, by `KeyGen.prefixWith_ok`) and y by the context's
comb (`comb`, by `KeyGen.tailWith_ok`), for a valid domain and its context.
-/

@[expose] public section

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
