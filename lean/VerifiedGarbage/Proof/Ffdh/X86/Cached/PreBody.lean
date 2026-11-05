module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreFront
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.ScanAt
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# FFDH's key-generation context on i686: the precomputation's body

`body_ok`: the width (`recognize_ok`, the bound's scan and bit length,
`cap_ok`) and its metadata, then p's context, rows 0 and 1 (`p` and
`R² mod p`) and the table (`table_ok`); the context's words are
`generationValues` (`values_of`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute
open VG.Impl.Ffdh.X86 (tbOff foundOff ldOff tOff)
open VG.Proof.Ffdh.KeyScalar (bnd)
open VG.Proof.Ffdh (lead)

/-! ## The width -/

/-- The bound's first significant byte is not zero. -/
theorem lead_ne {k : Nat} {dom : List Byte} (dv : Spec.Ffdh.domainValid k dom = true) (hk : 64 ≤ k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k) :
    (bnd k dom).getD (lead (bnd k dom)) 0 ≠ 0 := by
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hne : bnd k dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  obtain ⟨hodd, h1p, -⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod dv) hk
  have hld := VG.Proof.Ffdh.lead_lt hne
  rw [hbl] at hld
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) (by omega) size
    (fun _ => ⟨hodd, h1p⟩)
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    have hv := (VG.Proof.Ffdh.domainValid_iff k dom).mp dv
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  rw [← List.getElem_eq_getD (h := VG.Proof.Ffdh.lead_lt hne) 0]
  intro hb0
  by_cases hlast : lead (bnd k dom) + 1 < (bnd k dom).length
  · exact VG.Proof.Ffdh.lead_nonzero hne hlast hb0
  · rw [hb0] at hbits
    have : Spec.RsaKeyGen.bitLength (0 : Byte).toNat = 0 := rfl
    rw [this] at hbits
    have hpos := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega)).2
    rw [hbits] at hpos
    rw [hbl] at hlast
    have : k - lead (bnd k dom) - 1 = 0 := by omega
    rw [this] at hpos
    omega

/-- The width the code computes is `generationScalarBits`'s. -/
theorem width_spec {k : Nat} {dom : List Byte} (dv : Spec.Ffdh.domainValid k dom = true) (hk : 64 ≤ k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k) :
    pick (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom)
      (Spec.RsaKeyGen.bitLength ((bnd k dom).getD (lead (bnd k dom)) 0).toNat + 8 * (k - 1 - lead (bnd k dom))) =
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) := by
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hne : bnd k dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  obtain ⟨hodd, h1p, hnorm⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod dv) hk
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) (by omega) size
    (fun _ => ⟨hodd, h1p⟩)
  rw [List.getElem_eq_getD (h := VG.Proof.Ffdh.lead_lt hne) 0] at hbits
  have e : Spec.RsaKeyGen.bitLength ((bnd k dom).getD (lead (bnd k dom)) 0).toNat + 8 * (k - 1 - lead (bnd k dom)) =
      Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    rw [hbits]; omega
  rw [e, VG.Proof.Ffdh.VettedGroupFacts.recognize_spec (by omega) size hnorm]
  cases h : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp only [Option.getD_none, pick, ite_true, Spec.Ffdh.generationScalarBits, h]
  | some bits =>
    have bf := VG.Proof.Ffdh.ContextRows.recognized_nonzero h
    simp only [Option.getD_some, pick, bf, ite_false, Spec.Ffdh.generationScalarBits, h, Nat.min_def]
    by_cases c : bits < Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))
    · rw [ite_eq_left c, ite_eq_left (Nat.le_of_lt c)]
    · rw [ite_eq_right c]
      by_cases c' : bits ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))
      · rw [ite_eq_left c']; omega
      · rw [ite_eq_right c']

/-! ## The context's words -/

/-- A run of words from a longer one. -/
theorem val32_mid (m : Mem) (P : Addr) (d j k l : Nat) :
    val32 m P (d + 4 * j) k = val32 m P d (j + k + l) / 2 ^ (32 * j) % 2 ^ (32 * k) := by
  rw [val32_append m P d (j + k) l, val32_append m P d j k]
  have A := val32_lt m P d j
  have B := val32_lt m P (d + 4 * j) k
  rw [Nat.mul_add 32 j k, Nat.pow_add, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt A, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt B]

/-- The context's words from its 32-bit words: the width, its bytes and its rows, `p`, `R² mod p`
and the 32 entries. -/
theorem values_of {m : Mem} {args : Nat → BitVec 32} {len : Nat} {dom : List Byte}
    (bf : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) ≤ 8192)
    (h0 : w32 m (ctxAddr args) 0 = Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom))
    (h4 : w32 m (ctxAddr args) 4 = 0)
    (h8 : w32 m (ctxAddr args) 8 = (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) + 7) / 8)
    (h12 : w32 m (ctxAddr args) 12 = 0)
    (h16 : w32 m (ctxAddr args) 16 =
      Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom)))
    (h20 : w32 m (ctxAddr args) 20 = 0)
    (r0 : rowV m args len 0 = (Spec.Ffdh.domainOf len dom).p)
    (r1 : rowV m args len 1 = 2 ^ (16 * bc len .wide) % (Spec.Ffdh.domainOf len dom).p)
    (re : ∀ e < 32, rowV m args len (2 + e) = entV len (Spec.Ffdh.domainOf len dom).p (Spec.Ffdh.domainOf len dom).g
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom)) e) :
    Spec.Rsa.wordsAt m (ctxAddr args) (3 + 34 * mw len) = generationValues len dom := by
  have hb : bc len .wide = 8 * mw len := rfl
  have hc : cwc len .wide = 2 * mw len := by simp only [cwc, hb]; omega
  have rw' : ∀ j, VG.Proof.Ffdh.ContextRows.row m (ctxAddr args) (mw len) j =
      Spec.Rsa.toWords (rowV m args len j) (mw len) := fun j => by
    rw [VG.Proof.Ffdh.ContextRows.row_self, rowV, hc, VG.Proof.Ffdh.ContextRows.val32_eq_wv, hb,
      show 8 * mw len * j = 8 * (mw len) * j from rfl]
  have wd : ∀ {d v : Nat}, v < 2 ^ 64 → w32 m (ctxAddr args) d + 2 ^ 32 * w32 m (ctxAddr args) (d + 4) = v →
      VG.Proof.Bignum.word m (ctxAddr args) d = BitVec.ofNat 64 v := fun {d v} hv e => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    exact (word_eq_w32 m (ctxAddr args) d).trans e
  have rs := (VG.Proof.Rsa.FixedBaseComb.rows_small bf).1
  rw [VG.Proof.Ffdh.ContextRows.generationValues_parts]
  refine VG.Proof.Ffdh.ContextRows.ctx_words (wd (d := 0) (by omega) (by rw [h0, h4]; omega))
    (wd (d := 8) (by omega) (by rw [h8, h12]; omega)) (wd (d := 16) (by omega) (by rw [h16, h20]; omega)) ?_ ?_ fun e he => ?_
  · rw [rw', r0]
  · rw [rw', r1, show 16 * bc len .wide = 128 * mw len by rw [hb]; omega]
  · rw [rw', re e he, entV, enc, hb, show 8 * (8 * mw len) = 64 * mw len by omega]

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- Slot `a` to row `j` (0 or 1) of the context, which keeps the working space. -/
theorem storePre_ok {P : Nat} (Cx : CtxOk Ex base bytes len args .wide P s) (C : CtxW base bytes len args s)
    {j a : Nat} (hj : j < 2) (ha : a ≤ 27) :
    WP isa (storeRow (rowImm j) a) s fun t => CtxOk Ex base bytes len args .wide P t ∧ CtxW base bytes len args t ∧
      rowV t.mem args len j = sv s.mem base len .wide a ∧
      Outside (ctxAddr args) (24 + bc len .wide * j) (bc len .wide) s.mem t.mem ∧
      (∀ {d N : Nat}, d + 4 * N ≤ bytes → val32 t.mem base d N = val32 s.mem base d N) ∧
      Frame [ctxR args len] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have h := Cx.inp
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have bw := bc_eq_cwc len .wide
  refine WP.mono (storeRow_ok h C (j := j) (by omega) ha (rowImm_idx _)) fun t ⟨I, O, V, K⟩ => ?_
  have W : ∀ {d N : Nat}, d + 4 * N ≤ bytes → val32 t.mem base d N = val32 s.mem base d N :=
    fun hd => ws_far C bl (by omega) O hd
  have Wd : ∀ {d : Nat}, d + 4 ≤ bytes → w32 t.mem base d = w32 s.mem base d := fun {d} hd => by
    rw [← w32_val32_one, ← w32_val32_one]; exact W (by omega)
  have Ct : CtxOk Ex base bytes len args .wide P t := by
    have f0 := h.slot_fit .wide (j := 0) (by decide)
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    refine ⟨I, ?_, Cx.gt, Cx.odd, ?_⟩
    · show val32 _ _ _ _ = _; rw [W (by omega)]; exact Cx.mod
    · rw [Wd (by have := h.need; simp only [invOff, CrtRt.need] at *; omega)]; exact Cx.inv
  have rf := row_fit (len := len) (j := j) (by omega)
  have cw := C.ws.nowrap
  refine ⟨Ct, C.keep K, V, O, W, ?_, K.mono (by decide)⟩
  exact (Outside.frame_span O (by omega)).sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨ctxR args len, List.mem_singleton_self _, Offset.sub_base _ rf⟩

/-- The domain's bytes through writes of the context, the working space and the stack. -/
theorem dom_keepC (h : In Ex base bytes len args s) {dlen : Nat} {rd wr : List Region}
    (G : DomGeo args base bytes len dlen rd wr) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96))
    (domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)) {m m' : Mem}
    (F : Frame (ctxR args len :: frameR base sp (fR len)) m m') :
    Spec.Rsa.bytesAt m' (byteAddr (args 2)) dlen = Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen := by
  have := G.fit
  refine frame_bytes F (fun r hr => ?_) (by omega)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact domC
  · exact dom_frame h G hb40 r hr

/-- A component of the domain through writes of the context, the working space and the stack. -/
theorem comp_keepC (h : In Ex base bytes len args s) {dlen : Nat} {rd wr : List Region}
    (G : DomGeo args base bytes len dlen rd wr) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96))
    (domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)) {m m' : Mem}
    (F : Frame (ctxR args len :: frameR base sp (fR len)) m m') {k : Nat} (hk : k * len + len ≤ dlen) :
    comp m' args len k = comp m args len k := by
  have := G.fit
  unfold comp
  refine congrArg _ (frame_bytes F (fun r hr => ?_) (by omega))
  rcases List.mem_cons.mp hr with rfl | hr
  · exact domC.sub_left (Offset.sub_base _ hk)
  · exact (dom_frame h G hb40 r hr).sub_left (Offset.sub_base _ hk)

/-- A word of the context's header through the table. -/
theorem pre_word {m m' : Mem} (hp : preV m' args len = preV m args len) {i : Nat} (hi : i < 6) :
    w32 m' (ctxAddr args) (4 * i) = w32 m (ctxAddr args) (4 * i) := by
  have e : ∀ m : Mem, w32 m (ctxAddr args) (4 * i) = preV m args len / 2 ^ (32 * i) % 2 ^ (32 * 1) := fun m => by
    rw [← w32_val32_one, show 4 * i = 0 + 4 * i by omega, val32_mid m _ 0 i 1 (5 - i + 2 * cwc len .wide),
      show i + 1 + (5 - i + 2 * cwc len .wide) = 6 + 2 * cwc len .wide by omega]
  rw [e, e, hp]

/-- Row 0 or 1 of the context through the table. -/
theorem pre_row {m m' : Mem} (hp : preV m' args len = preV m args len) {j : Nat} (hj : j < 2) :
    rowV m' args len j = rowV m args len j := by
  have bw := bc_eq_cwc len .wide
  have e : ∀ m : Mem, rowV m args len j =
      preV m args len / 2 ^ (32 * (6 + cwc len .wide * j)) % 2 ^ (32 * cwc len .wide) := fun m => by
    rw [rowV, show 24 + bc len .wide * j = 0 + 4 * (6 + cwc len .wide * j) by rw [bw, Nat.mul_assoc]; omega,
      val32_mid m _ 0 (6 + cwc len .wide * j) (cwc len .wide) (cwc len .wide - cwc len .wide * j),
      show 6 + cwc len .wide * j + cwc len .wide + (cwc len .wide - cwc len .wide * j) = 6 + 2 * cwc len .wide by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> omega]
  rw [e, e, hp]

/-- The precomputation's body: the context of the domain, and 1. -/
theorem body_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)) (C : CtxW base bytes len args s)
    {T : BitVec 32} (hT : s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T) (tfit : T.toNat + 17744 ≤ 2 ^ 32)
    (tread : InRegions (s.rd ++ s.wr) (byteAddr T) 17744)
    (tbytes : Spec.Rsa.bytesAt s.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes)
    (tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩)
    (t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below (s.gpr .esp) 96))
    (dv : Spec.Ffdh.domainValid len (KeyGen.domOf s.mem args dlen) = true) :
    WP isa Precompute.body s fun t => t.gpr .eax = 1 ∧
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      Spec.Rsa.wordsAt t.mem (ctxAddr args) (3 + 34 * mw len) = generationValues len (KeyGen.domOf s.mem args dlen) := by
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have dfit := G.fit
  have h2 : 2 * len ≤ dlen := by omega
  generalize hD : KeyGen.domOf s.mem args dlen = dom at dv
  have size : dom.length = 2 * len ∨ dom.length = 3 * len := by
    rw [← hD, VG.Proof.Bignum.bytesAt_length]; exact dl
  obtain ⟨hodd, h1p, -⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod dv) lw
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  have hp : comp s.mem args len 0 = (Spec.Ffdh.domainOf len dom).p := by rw [comp_p s.mem args h2, ← hD]
  have hg : comp s.mem args len 1 = (Spec.Ffdh.domainOf len dom).g := by rw [comp_g s.mem args h2, ← hD]
  have up' : ∀ {m m' : Mem}, Frame [ctxR args len] m m' →
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) m m' :=
    fun F => F.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..
  have upB : ∀ {m m' : Mem}, Frame (frameR base (s.gpr .esp) (fR len)) m m' →
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) m m' :=
    fun F => F.mono fun r hr => List.mem_cons_of_mem _ hr
  unfold Precompute.body
  -- The recognized width.
  refine WP.seq (WP.mono (recognize_ok h G hb40 hT tfit tread tbytes tws t40) fun u₁ ⟨S₁, k₁, r₁⟩ => ?_)
  rw [show Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen = dom from hD] at r₁
  have sp₁ := S₁.esp
  -- The bound's first significant byte and its mask.
  have G₁ := G.keep ⟨rfl, rfl⟩ S₁.keeps
  refine WP.seq (WP.mono (KeyScan.scan_ok S₁.inp G.e3 (KeyGen.bound_geo G₁ (by rw [sp₁]; exact hb40)))
    fun u₂ Sc => ?_)
  have bs : Spec.Rsa.bytesAt u₁.mem (byteAddr (KeyScan.boundAt args)) len = bnd len dom := by
    rw [KeyGen.bound_bytes G, dom_keep h G hb40 S₁.frame]; exact congrArg _ hD
  rw [bs] at Sc
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hne : bnd len dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  have hld : lead (bnd len dom) < len := by have := VG.Proof.Ffdh.lead_lt hne; rwa [hbl] at this
  generalize hb : (bnd len dom).getD (lead (bnd len dom)) 0 = b at Sc
  have b0 : b ≠ 0 := hb ▸ lead_ne dv lw size
  have bt : b.toNat ≠ 0 := fun e => b0 (BitVec.eq_of_toNat_eq e)
  have hn := VG.Proof.Ffdh.KeyScalar.bitLength_bounds bt
  have hn1 : 1 ≤ Spec.RsaKeyGen.bitLength b.toNat := by
    simp only [Spec.RsaKeyGen.bitLength, bt, ↓reduceIte]; omega
  have hn8 : Spec.RsaKeyGen.bitLength b.toNat ≤ 8 := by
    have := b.isLt
    by_contra hc
    have : 2 ^ 8 ≤ 2 ^ (Spec.RsaKeyGen.bitLength b.toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have S₁₂ := S₁.trans Sc.step
  -- Its bit length.
  refine WP.seq (WP.mono (maskBits_ok Sc.step.inp (n := Spec.RsaKeyGen.bitLength b.toNat) hn1 hn8
    (by rw [Sc.t, hb, VG.Proof.Ffdh.KeyScalar.smearN_eq _ b.isLt])) fun u₃ ⟨e₃, m₃, K₃⟩ => ?_)
  have h₃ := Sc.step.inp.regs K₃ m₃
  refine WP.seq (WP.mono (boundBits_ok h₃ G.e3 (ld := lead (bnd len dom)) (by rw [m₃]; exact Sc.ld) hld e₃)
    fun u₄ ⟨e₄, m₄, K₄⟩ => ?_)
  have h₄ := h₃.regs K₄ m₄
  -- The width.
  have rec₄ : w32 u₄.mem base recOff =
      VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len dom := by
    rw [m₄, m₃, Sc.kept.word_eq (by simp only [recOff, numBase]; decide)]; exact r₁
  refine WP.seq (WP.mono (cap_ok h₄ rec₄ (recognize_lt _ _) e₄ (by omega)) fun u₅ ⟨e₅, m₅, K₅⟩ => ?_)
  have h₅ := h₄.regs K₅ m₅
  rw [show Spec.RsaKeyGen.bitLength b.toNat + 8 * (len - 1 - lead (bnd len dom)) =
      Spec.RsaKeyGen.bitLength ((bnd len dom).getD (lead (bnd len dom)) 0).toNat + 8 * (len - 1 - lead (bnd len dom))
      by rw [hb], width_spec dv lw size] at e₅
  generalize hW : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) = W at e₅ bf
  have bW : W ≤ 8192 := by omega
  -- The metadata.
  have K₁₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ :=
    S₁₂.keeps.trans ((K₃.mono (by decide)).trans ((K₄.mono (by decide)).trans (K₅.mono (by decide))))
  have m₂₅ : u₅.mem = u₂.mem := by rw [m₅, m₄, m₃]
  have sp₅ : u₅.gpr .esp = s.gpr .esp := K₁₅.1 _ (by decide)
  refine WP.seq (WP.mono (metadata_ok h₅ (C.keep K₁₅) e₅ bW)
    fun u₆ ⟨h₆, C₆, F₆, K₆, _, wr₆, c0, c4, c8, c12, c16, c20⟩ => ?_)
  rw [sp₅, m₂₅] at F₆
  have FA₆ : Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) s.mem u₆.mem := (upB S₁₂.frame).trans F₆
  have K₁₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₆ := K₁₅.trans (K₆.mono (by decide))
  have sp₆ : u₆.gpr .esp = s.gpr .esp := K₁₆.1 _ (by decide)
  have G₆ := G.keep ⟨rfl, rfl⟩ K₁₆
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h₆ G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G₆.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega)))) fun u₇ ⟨h₇, F₇, k₇, v9, _, _, K₇⟩ => ?_)
  rw [CheckDomain.argNum_comp, comp_keepC h G hb40 domC FA₆ (by omega), hp] at v9
  rw [sp₆] at F₇
  have FA₇ := FA₆.trans (upB F₇)
  have K₁₇ := K₁₆.trans K₇
  -- g.
  refine WP.seq (WP.mono (loadComp_ok h₇ (G.keep ⟨rfl, rfl⟩ K₁₇) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₈ ⟨v10, O₈, K₈⟩ => ?_)
  rw [comp_keepC h G hb40 domC FA₇ (by omega), hg] at v10
  have S₈ : Step Ex base bytes len args u₇ u₈ := Step.slot h₇ (by decide) O₈ K₈
  have k₈ := kept_slot h₇ (a := 10) O₈
  have sp₇ : u₇.gpr .esp = s.gpr .esp := K₁₇.1 _ (by decide)
  have F₈ := S₈.frame
  rw [sp₇] at F₈
  have FA₈ := FA₇.trans (upB F₈)
  have K₁₈ := K₁₇.trans S₈.keeps
  -- p's context.
  have v9₈ : sv u₈.mem base len .wide 9 = (Spec.Ffdh.domainOf len dom).p := by rw [k₈.slot_eq]; exact v9
  refine WP.seq (WP.mono (ctxP_ok S₈.inp (P := (Spec.Ffdh.domainOf len dom).p) (by rw [v9₈]; exact safeM_of h1p hodd))
    fun u₉ ⟨Cx₉, s3, s4, F₉, k₉, K₉⟩ => ?_)
  have sp₈ : u₈.gpr .esp = s.gpr .esp := K₁₈.1 _ (by decide)
  rw [sp₈] at F₉
  have FA₉ := FA₈.trans (upB (fR_widen F₉ (stR_inF S₈.inp)))
  have K₁₉ := K₁₈.trans K₉
  -- Rows 0 and 1: p and `R² mod p`.
  refine WP.seq (WP.mono (storePre_ok Cx₉ (C.keep K₁₉) (j := 0) (a := 9) (by decide) (by decide))
    fun u₁₀ ⟨Cx₁₀, C₁₀, rv₁₀, O₁₀, W₁₀, F₁₀, K₁₀⟩ => ?_)
  refine WP.seq (WP.mono (storePre_ok Cx₁₀ C₁₀ (j := 1) (a := 4) (by decide) (by decide))
    fun u₁₁ ⟨Cx₁₁, C₁₁, rv₁₁, O₁₁, W₁₁, F₁₁, K₁₁⟩ => ?_)
  have FA₁₁ := (FA₉.trans (up' F₁₀)).trans (up' F₁₁)
  have K₁₁' := (K₁₉.trans K₁₀).trans K₁₁
  have sw : ∀ {j : Nat}, j ≤ 27 → sv u₁₁.mem base len .wide j = sv u₉.mem base len .wide j := fun {j} hj => by
    have := Cx₉.inp.slot_fit .wide (j := j) hj
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    have bw := bc_eq_cwc len .wide
    show val32 _ _ _ _ = val32 _ _ _ _
    rw [W₁₁ (by omega), W₁₀ (by omega)]
  have rows₁₁ : w32 u₁₁.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows W := by
    rw [← w32_val32_one, W₁₁ (by simp only [rowsOff]; omega), W₁₀ (by simp only [rowsOff]; omega), w32_val32_one,
      k₉.word_eq (by simp only [rowsOff, numBase]; decide), k₈.word_eq (by simp only [rowsOff, numBase]; decide),
      k₇.word_eq (by simp only [rowsOff, numBase]; decide)]
    exact wr₆
  -- The table.
  have S₀ : TS Ex base bytes len args (Spec.Ffdh.domainOf len dom).p (Spec.Ffdh.domainOf len dom).g W u₁₁ 0 u₁₁ :=
    ⟨Cx₁₁, C₁₁, by omega, fun e he => absurd he (Nat.not_lt_zero _), rows₁₁, rfl, Frame.refl _ _, Keeps.refl _ _⟩
  have rs := VG.Proof.Rsa.FixedBaseComb.rows_small bW
  refine WP.seq (WP.mono (table_ok S₀ (by rw [sw (by decide)]; exact s3) (by rw [sw (by decide)]; exact s4)
    (by rw [sw (by decide), k₉.slot_eq]; exact v10) (VG.Proof.Rsa.FixedBaseComb.rows_pos (by omega)) rs.1)
    fun u₁₂ S₁₂' => WP.mono ret_ok fun t ⟨et, mt, Kt⟩ => ?_)
  have sp₁₁ : u₁₁.gpr .esp = s.gpr .esp := K₁₁'.1 _ (by decide)
  have F₁₂ := S₁₂'.frame
  rw [sp₁₁] at F₁₂
  refine ⟨by rw [et]; rfl, by rw [mt]; exact FA₁₁.trans F₁₂, K₁₁'.trans (S₁₂'.keeps.trans (Kt.mono (by decide))), ?_⟩
  -- The context's words.
  have bw := bc_eq_cwc len .wide
  have bg := bc_ge lw .wide
  have cbn : ctxBytes len = 24 + bc len .wide * 34 := rfl
  have cw := C.ws.nowrap
  have F69 : Frame (frameR base (s.gpr .esp) (fR len)) u₆.mem u₉.mem :=
    (F₇.trans F₈).trans (fR_widen F₉ (stR_inF S₈.inp))
  have hdr : ∀ i, i < 6 → w32 t.mem (ctxAddr args) (4 * i) = w32 u₆.mem (ctxAddr args) (4 * i) := fun i hi => by
    rw [mt, pre_word S₁₂'.pre hi, O₁₁.w32 (.inl (by omega)) (by omega), O₁₀.w32 (.inl (by omega)) (by omega),
      ← w32_val32_one, ← w32_val32_one, ctx_far C F69 (fR_fit h) (by omega)]
  have r0 : rowV t.mem args len 0 = (Spec.Ffdh.domainOf len dom).p := by
    rw [mt, pre_row S₁₂'.pre (by decide)]
    show val32 _ _ _ _ = _
    rw [O₁₁.val32 (.inl (by omega)) (by omega)]
    rw [show val32 u₁₀.mem (ctxAddr args) (24 + bc len .wide * 0) (cwc len .wide) = rowV u₁₀.mem args len 0 from rfl,
      rv₁₀, k₉.slot_eq]
    exact v9₈
  have r1 : rowV t.mem args len 1 = 2 ^ (16 * bc len .wide) % (Spec.Ffdh.domainOf len dom).p := by
    rw [mt, pre_row S₁₂'.pre (by decide), rv₁₁]
    have := Cx₉.inp.slot_fit .wide (j := 4) (by decide)
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    show val32 _ _ _ _ = _
    rw [W₁₀ (by omega)]
    exact s4
  have e0 := hdr 0 (by decide)
  have e1 := hdr 1 (by decide)
  have e2 := hdr 2 (by decide)
  have e3 := hdr 3 (by decide)
  have e4 := hdr 4 (by decide)
  have e5 := hdr 5 (by decide)
  rw [c0] at e0
  rw [c4] at e1
  rw [c8] at e2
  rw [c12] at e3
  rw [c16] at e4
  rw [c20] at e5
  subst hW
  refine values_of bW e0 e1 e2 e3 e4 e5 r0 r1 fun e he => ?_
  rw [mt]; exact S₁₂'.ents e he

end

end VG.Proof.Ffdh.X86.Cached
