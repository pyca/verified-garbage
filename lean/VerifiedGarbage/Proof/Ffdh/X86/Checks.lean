module

public import VerifiedGarbage.Proof.Ffdh.X86.Dom
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Ffdh.X86.Ops

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
    exact G.apart.sub_right (Offset.sub_base _ (by omega))

/-- The domain's bytes after a stage. -/
theorem dom_keep (h : In Ex base bytes len args s) {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    {sp : BitVec 32} (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) {m m' : Mem}
    (F : Frame (frameR base sp (fR len)) m m') :
    Spec.Rsa.bytesAt m' (byteAddr (args 2)) dlen = Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen :=
  frame_bytes F (dom_frame h G hb40) (by have := G.fit; omega)

/-- A component after a stage. -/
theorem comp_keep (h : In Ex base bytes len args s) {rd wr : List Region} (G : DomGeo args base bytes len dlen rd wr)
    {sp : BitVec 32} (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)) {m m' : Mem}
    (F : Frame (frameR base sp (fR len)) m m') {k : Nat} (hk : k * len + len ≤ dlen) :
    comp m' args len k = comp m args len k := by
  have := G.fit
  unfold comp
  rw [frame_bytes F (fun r hr => (dom_frame h G hb40 r hr).sub_left (Offset.sub_base _ hk)) (by omega)]

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
    · rw [decide_eq_true rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega),
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), show 2 * len - len - len = 0 by omega]
      rfl
    · rw [decide_eq_false (by omega), BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega),
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), show 3 * len - len - len = len by omega]
      apply beq_eq_false_iff_ne.mpr
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by show len ≠ 0; omega)
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
    (by rw [cb1] at f; omega) fun v Kv mv pv => ?_
  have hv := h.regs Kv mv
  have ld := VG.Proof.Mont.X86.Rt.readSrc_ptr hv.ws pv (d := 0) (by rw [cb1] at f; omega)
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
      omega
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
