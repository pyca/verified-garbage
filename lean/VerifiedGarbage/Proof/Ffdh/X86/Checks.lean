module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Ffdh.Contract

/-! ### `Ffdh.X86.Dom`, which this module and modules that import it used -/

section

/-!
# FFDH on i686: the domain's components

`DomGeo`: the domain buffer of `dlen` bytes at synthetic argument 2, its
components p, g and q (`p_len` bytes each) at arguments 2, 4 and 6, with
their lengths. `loadComp_ok`: the `k`-th component into a wide slot, the
value `domainOf` gives it (`comp_p`, `comp_g`, `comp_q`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen : Nat}
  {args : Nat → BitVec 32}

/-- The domain buffer and its components, as the synthetic arguments give them. -/
structure DomGeo (args : Nat → BitVec 32) (base : Addr) (bytes len dlen : Nat) (rd wr : List Region) : Prop where
  e3 : args 3 = BitVec.ofNat 32 len
  e5 : args 5 = BitVec.ofNat 32 len
  e7 : args 7 = BitVec.ofNat 32 len
  e4 : args 4 = args 2 + args 3
  e6 : args 6 = args 2 + args 3 + args 3
  e12 : args 12 = BitVec.ofNat 32 dlen
  dl : dlen = 2 * len ∨ dlen = 3 * len
  fit : (args 2).toNat + dlen ≤ 2 ^ 32
  rd : InRegions (rd ++ wr) (byteAddr (args 2)) dlen
  apart : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨base, bytes⟩
  lower : 64 ≤ len
  upper : len ≤ 1024

theorem DomGeo.keep {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) {s t : State} {rs : List Reg}
    (e : s.rd = rd ∧ s.wr = wr) (K : Keeps rs s t) : DomGeo args base bytes len dlen t.rd t.wr := by
  rw [K.2.1, K.2.2, e.1, e.2]; exact G

/-- The `k`-th component's address. -/
theorem DomGeo.addr {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr) {k : Nat} (hk : k ≤ 2)
    (hkl : (k + 1) * len ≤ dlen) :
    byteAddr (args (2 + 2 * k)) = byteAddr (args 2) + BitVec.ofNat 64 (k * len) ∧
      (args (2 + 2 * k)).toNat = (args 2).toNat + k * len := by
  have f := G.fit
  have l := G.upper
  have e3 : (args 3).toNat = len := by rw [G.e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [l])]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega_using [hk]) with rfl | rfl | rfl
  · simp
  · rw [show 2 + 2 * 1 = 4 from rfl, G.e4, G.e3, byteAddr_add (by omega_using [f, hkl])]
    refine ⟨by simp, ?_⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := len) (by omega_using [l]), Nat.mod_eq_of_lt (by omega_using [f, hkl])]
    omega_using []
  · rw [show 2 + 2 * 2 = 6 from rfl, G.e6, G.e3, byteAddr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := len) (by omega_using [l]), Nat.mod_eq_of_lt (by omega_using [f, hkl])]; omega_using [f, hkl]), byteAddr_add (by omega_using [f, hkl]),
      VG.Offset.add_add]
    refine ⟨by congr 2; omega_using [], ?_⟩
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := len) (by omega_using [l]),
      Nat.mod_eq_of_lt (a := (args 2).toNat + len) (by omega_using [f, hkl]), Nat.mod_eq_of_lt (by omega_using [f, hkl])]
    omega_using []

/-- The value of the `k`-th component. -/
abbrev comp (m : Mem) (args : Nat → BitVec 32) (len k : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2) + BitVec.ofNat 64 (k * len)) len)

/-- The `k`-th component into the wide slot `j`. -/
theorem loadComp_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr) {k j : Nat}
    (hk : k ≤ 2) (hkl : (k + 1) * len ≤ dlen) (hj : j ≤ 19) :
    WP isa (load (.slot .wide j) (one .wide) (2 + 2 * k) (3 + 2 * k)) s fun u =>
      sv u.mem base len .wide j = comp s.mem args len k ∧
      Outside base (lo len (.slot .wide j)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  obtain ⟨ea, en⟩ := G.addr hk hkl
  have f := G.fit
  have l := G.upper
  have lb := len_le_bc len
  have lw := G.lower
  have hl : args (3 + 2 * k) = BitVec.ofNat 32 len := by
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega_using [hk]) with rfl | rfl | rfl
    · exact G.e3
    · exact G.e5
    · exact G.e7
  have hkl' : k * len + len ≤ dlen := by rw [Nat.succ_mul] at hkl; exact hkl
  have rd : InRegions (s.rd ++ s.wr) (byteAddr (args (2 + 2 * k))) len := by
    rw [ea]; exact VG.CallLay.inRegions_sub G.rd (by omega_using [hkl']) (by omega_using [f])
  have apart : Region.Disjoint ⟨byteAddr (args (2 + 2 * k)), len⟩ ⟨base, bytes⟩ := by
    rw [ea]; exact G.apart.sub_left (Offset.sub_base _ (by omega_using [hkl']))
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := j) (by omega_using [hj])) (p := 2 + 2 * k) (l := 3 + 2 * k)
    (L := len) (by omega_using [hk]) (by omega_using [hk]) hl (by omega_using [lw]) (by rw [cb1]; exact lb) (by omega_using [en, f, hkl']) rd apart)
    fun u ⟨V, O, K⟩ => ⟨by rw [cw1, ea] at V; exact V, by rw [cb1] at O; exact O, K⟩

/-- The components are `domainOf`'s p, g and q. -/
theorem comp_p (m : Mem) (args : Nat → BitVec 32) (h : 2 * len ≤ dlen) :
    comp m args len 0 = (Spec.Ffdh.domainOf len (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen)).p := by
  rw [VG.Proof.Ffdh.domainOf_p m _ h, comp, Nat.zero_mul]; congr 2; exact BitVec.add_zero _

theorem comp_g (m : Mem) (args : Nat → BitVec 32) (h : 2 * len ≤ dlen) :
    comp m args len 1 = (Spec.Ffdh.domainOf len (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen)).g := by
  rw [VG.Proof.Ffdh.domainOf_g m _ h, comp, Nat.one_mul]

theorem comp_q (m : Mem) (args : Nat → BitVec 32) :
    (Spec.Ffdh.domainOf len (Spec.Rsa.bytesAt m (byteAddr (args 2)) (3 * len))).q = some (comp m args len 2) := by
  rw [VG.Proof.Ffdh.domainOf_q3, comp, Nat.mul_comm 2 len]

end VG.Proof.Ffdh.X86

end

end

/-!
# FFDH on i686: what the checks read

The domain's bytes, apart from what a stage changes, keep their value
(`frame_bytes`, `comp_keep`); `qTest` tells whether the domain has a q
(`qTest_ok`); `oddMask` and-s the mask with q's low bit (`oddMask_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen : Nat}
  {args : Nat → BitVec 32}

/-- Bytes apart from the regions a frame changes keep their values. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (F : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact F.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The domain apart from a stage's changes: the working space and the 96 bytes below `sp`. -/
theorem dom_frame (h : In Ex base bytes len args s) {rd wr : List Region}
    (G : DomGeo args base bytes len dlen rd wr) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) :
    ∀ r ∈ frameR base sp (fR len), Region.Disjoint ⟨byteAddr (args 2), dlen⟩ r := by
  have fit := fR_fit h
  have bl := h.bytes_lt
  intro r hr
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact hb40
  · have := fit p hp
    exact G.apart.sub_right (Offset.sub_base _ (by omega_using [this]))

/-- The domain's bytes after a stage. -/
theorem dom_keep (h : In Ex base bytes len args s) {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    {sp : BitVec 32} (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) {m m' : Mem}
    (F : Frame (frameR base sp (fR len)) m m') :
    Spec.Rsa.bytesAt m' (byteAddr (args 2)) dlen = Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen :=
  frame_bytes F (dom_frame h G hb40) (by have := G.fit; omega_using [this])

/-- A component after a stage. -/
theorem comp_keep (h : In Ex base bytes len args s) {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    {sp : BitVec 32} (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) {m m' : Mem}
    (F : Frame (frameR base sp (fR len)) m m') {k : Nat} (hk : k * len + len ≤ dlen) :
    comp m' args len k = comp m args len k := by
  have := G.fit
  unfold comp
  rw [frame_bytes F (fun r hr => (dom_frame h G hb40 r hr).sub_left (Offset.sub_base _ hk)) (by omega_using [hk, this])]

/-- `domain_len − 2 p_len`: ZF set exactly when the domain has no q. -/
theorem qTest_ok (h : In Ex base bytes len args s) (h3 : args 3 = BitVec.ofNat 32 len)
    (h12 : args 12 = BitVec.ofNat 32 dlen) (hd : dlen = 2 * len ∨ dlen = 3 * len) :
    WP isa (.block Impl.Ffdh.X86.qTest) s fun u =>
      isa.eval .e u = some (decide (dlen = 2 * len)) ∧ u.mem = s.mem ∧ Keeps [.eax] s u := by
  have hu := h.upper'
  have hl := h.lower'
  unfold Impl.Ffdh.X86.qTest
  refine wp_movS (h.arg (i := 12) (by decide)) fun u₁ U₁ _ => ?_
  have h₁ := h.regs U₁.keeps U₁.mem
  refine wp_subS (h₁.arg (i := 3) (by decide)) fun u₂ U₂ _ => ?_
  have h₂ := h₁.regs U₂.keeps U₂.mem
  refine wp_subZ (h₂.arg (i := 3) (by decide)) fun u U z => WP.block_nil ⟨?_, ?_, ?_⟩
  · show u.zf = _
    rw [z, U₂.gpr, U₁.gpr, h12, h3]
    congr 1
    rcases hd with rfl | rfl
    · rw [decide_eq_true rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu]) (by omega_using []),
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu]) (by omega_using []), show 2 * len - len - len = 0 by omega_using []]
      rfl
    · rw [decide_eq_false (by omega_using [hl]), BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu]) (by omega_using []),
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hu]) (by omega_using []), show 3 * len - len - len = len by omega_using []]
      apply beq_eq_false_iff_ne.mpr
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hu])] at this
      exact absurd this (by show len ≠ 0; omega_using [hl])
  · rw [U.mem, U₂.mem, U₁.mem]
  · exact ((U₁.keeps.trans U₂.keeps).trans U.keeps)

/-- `ecx` and-ed with all ones if the wide slot 11's number is odd, else zero. -/
theorem oddMask_ok (h : In Ex base bytes len args s) {c : Bool} (hc : s.gpr .ecx = cmask c) :
    WP isa (.block Impl.Ffdh.X86.CheckDomain.oddMask) s fun u =>
      u.gpr .ecx = cmask (c && decide (sv s.mem base len .wide 11 % 2 = 1)) ∧ u.mem = s.mem ∧
        Keeps [.eax, .ecx, .edx] s u := by
  have f := slot_fit1 h (j := 11) (by decide)
  have bl := h.bytes_lt
  have g := bc_ge h.lower' .wide
  have bw := bc_eq_cwc len .wide
  unfold Impl.Ffdh.X86.CheckDomain.oddMask
  refine ptrTo_ok (r := .eax) (t := .edx) (x := .slot .wide 11) (by decide) (by decide) h.edi h.width h.upper'
    (by rw [cb1] at f; omega_using [f, bl]) fun v Kv mv pv => ?_
  have hv := h.regs Kv mv
  have ld := VG.Proof.Mont.X86.Rt.readSrc_ptr hv.ws pv (d := 0) (by rw [cb1] at f; omega_using [f, g])
  rw [Nat.add_zero, mv] at ld
  refine wp_movS ld fun v₁ U₁ _ => wp_logicS (.inl rfl) rfl fun v₂ U₂ => wp_movS rfl fun v₃ U₃ _ => ?_
  refine wp_subS rfl fun v₄ U₄ _ => wp_logicS (.inl rfl) rfl fun u U => WP.block_nil ⟨?_, ?_, ?_⟩
  · have hodd : (s.mem.readW (off base (lo len (.slot .wide 11))) 32).toNat % 2 =
        sv s.mem base len .wide 11 % 2 := by
      have hw : 1 ≤ cwc len .wide := by omega
      have e : sv s.mem base len .wide 11 =
          val32 s.mem base (lo len (.slot .wide 11)) (1 + (cwc len .wide - 1)) := by
        rw [Nat.add_sub_cancel' hw]
      rw [e, val32_append, w32_val32_one, Nat.mul_one]
      show _ = ((s.mem.readW (off base (lo len (.slot .wide 11))) 32).toNat + _) % 2
      have p32 : (2 : Nat) ^ 32 = 4294967296 := rfl
      rw [p32]
      omega_using []
    have e4 : v₄.gpr .edx = cmask (decide (sv s.mem base len .wide 11 % 2 = 1)) := by
      rw [U₄.gpr, U₃.gpr, U₃.other _ (by decide), U₂.gpr]
      simp only [↓reduceIte]
      rw [U₁.gpr, zero_sub_and_one, hodd]
    rw [U.gpr]
    simp only [↓reduceIte]
    rw [e4, U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide),
      Kv.1 _ (by decide), hc, cmask_and]
  · rw [U.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem, mv]
  · exact (Kv.mono (by decide)).trans ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (U₃.keeps.mono (by decide))).trans ((U₄.keeps.mono (by decide)).trans (U.keeps.mono (by decide))))

end VG.Proof.Ffdh.X86
