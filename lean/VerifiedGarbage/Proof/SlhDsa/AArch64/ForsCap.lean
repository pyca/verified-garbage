module

-- separate module: the capture of the private key values and the leaves to the nodes, stages of `forsSign`'s proof rebuilt only when they change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsLeaf
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`, the capture and the nodes of four leaves

The second and last blocks of `leafBody` (`Impl/SlhDsa/AArch64/Fors.lean`):
each lane's private key value XORed into the signature's at `x24` under the
mask of its leaf being the tree's index (`captureSk`, `capB_ok`), with the
lanes' type then `FORS_TREE`; and the four outputs to the nodes `J` to
`J + 3`, the next `J` (`out_ok`). As x86-64's
(`Proof/SlhDsa/X86_64/ForsLeaf.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

variable {p : Params}

theorem upK {s s' : State} {d : Reg} {x : BitVec 64} (h : Up s s' d x) : Keep [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr, h.sp, fun r _ => by rw [h.v]⟩

theorem muK {s s' : State} {m : Mem} (h : Mu s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, fun r _ => by rw [h.v]⟩

/-! ## The masked XOR of a lane into the signature -/

/-- What the masked XOR of `len` bytes at `src` into those at `dst` leaves:
`src`'s bytes XORed in if `c`, nothing if not. -/
structure XorPost (c : Prop) [Decidable c] (s s' : State) (dst src : Addr) (len : Nat) : Prop where
  keep : Keep [.x13, .x14] s s'
  bytes : ∀ q < len, s'.mem (dst + BitVec.ofNat 64 q) =
    (if c then s.mem (src + BitVec.ofNat 64 q) else 0) ^^^ s.mem (dst + BitVec.ofNat 64 q)
  frame : Frame [⟨dst, len⟩] s.mem s'.mem

theorem XorPost.trans {c : Prop} [Decidable c] {s s₁ s₂ : State} {D Sr : Addr} {a e : Nat}
    (h₁ : XorPost c s s₁ D Sr a) (h₂ : XorPost c s₁ s₂ (D + BitVec.ofNat 64 a) (Sr + BitVec.ofNat 64 a) e)
    (hdis : Region.Disjoint ⟨D, a + e⟩ ⟨Sr, a + e⟩) (hae : a + e < 2 ^ 64) : XorPost c s s₂ D Sr (a + e) := by
  refine ⟨(h₁.keep.trans h₂.keep).mono (by simp), fun q hq => ?_, ?_⟩
  · by_cases cq : q < a
    · rw [h₂.frame.bytes (R := ⟨D, a⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint D (Nat.le_refl a) (by omega_using [hae])) (by show a ≤ 2 ^ 64; omega_using [hae]) cq,
        h₁.bytes q cq]
    · have e₁ : D + BitVec.ofNat 64 q = D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) := by
        rw [Blocks.ofNat_add', Nat.add_sub_cancel' (by omega_using [cq])]
      have e₂ : Sr + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) = Sr + BitVec.ofNat 64 q := by
        rw [Blocks.ofNat_add', Nat.add_sub_cancel' (by omega_using [cq])]
      have fs : s₁.mem (Sr + BitVec.ofNat 64 q) = s.mem (Sr + BitVec.ofNat 64 q) :=
        h₁.frame.bytes (R := ⟨Sr, a + e⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hdis.symm.sub_right (Region.sub_prefix (Nat.le_add_right a e))) (by show a + e ≤ 2 ^ 64; omega_using [hae]) hq
      have fd : s₁.mem (D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a)) =
          s.mem (D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a)) :=
        h₁.frame.bytes (R := ⟨D + BitVec.ofNat 64 a, e⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (Nat.le_refl a) (by omega_using [hae])) (by show e ≤ 2 ^ 64; omega_using [hae])
          (by show q - a < e; omega_using [hq, cq])
      rw [e₁, h₂.bytes _ (by omega_using [hq, cq]), e₂, fs, fd]
  · refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (Nat.le_add_right a e)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base D (Nat.le_refl _)⟩

/-- A byte of a word XORed with a masked word. -/
theorem xmask_byte (c : Prop) [Decidable c] (lw sw : BitVec 64) (q : Nat) :
    (sw ^^^ (lw &&& (if c then BitVec.allOnes 64 else 0))).extractLsb' (8 * q) 8 =
      (if c then lw.extractLsb' (8 * q) 8 else 0) ^^^ sw.extractLsb' (8 * q) 8 := by
  by_cases h : c
  · simp only [h, ↓reduceIte, BitVec.and_allOnes, BitVec.extractLsb'_xor, BitVec.xor_comm]
  · simp [h]

/-- The word of a lane of the masked XOR. -/
abbrev xorWord (dst src : Reg) (D w : Nat) : List Instr :=
  [.ldr .x .x13 src (D + 8 * w), .logic .and .x .x13 .x13 .x12,
    .ldr .x .x14 dst (8 * w), .logic .eor .x .x14 .x14 .x13, .str .x .x14 dst (8 * w)]

section
variable {s : State}

theorem xor8_ok {dst src : Reg} (hd : dst ≠ .x13 ∧ dst ≠ .x14) {c : Prop} [Decidable c]
    (hm : s.gpr .x12 = if c then BitVec.allOnes 64 else 0) {D w : Nat} (h₁ : (D + 8 * w) % 8 = 0 ∧ D + 8 * w < 32768)
    (h₂ : 8 * w < 32768) (hsrc : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (D + 8 * w)) 8)
    (hdst : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (8 * w)) 8) :
    WP isa (.block (xorWord dst src D w)) s
      (fun s' => XorPost c s s' (s.gpr dst + BitVec.ofNat 64 (8 * w)) (s.gpr src + BitVec.ofNat 64 (D + 8 * w)) 8) := by
  have hdst' : InRegions (s.rd ++ s.wr) (s.gpr dst + BitVec.ofNat 64 (8 * w)) 8 := by
    obtain ⟨r, h, c⟩ := hdst; exact ⟨r, List.mem_append_right _ h, c⟩
  refine wp_ldr h₁ rfl hsrc fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  refine wp_ldr ⟨by omega_using [], h₂⟩ (by rw [u₂.other _ hd.1, u₁.other _ hd.1])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hdst') fun s₃ u₃ => wp_eor fun s₄ u₄ => ?_
  refine wp_str ⟨by omega_using [], h₂⟩ (by
      rw [u₄.other _ hd.2, u₃.other _ hd.2, u₂.other _ hd.1, u₁.other _ hd.1])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hdst) fun s₅ u₅ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hv : s₄.gpr .x14 = s.mem.readW (s.gpr dst + BitVec.ofNat 64 (8 * w)) 64 ^^^
      (s.mem.readW (s.gpr src + BitVec.ofNat 64 (D + 8 * w)) 64 &&& (if c then BitVec.allOnes 64 else 0)) := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hm, u₂.mem, u₁.mem]
  refine ⟨(((upK u₁).trans (upK u₂)).trans (((upK u₃).trans (upK u₄)).trans (muK u₅))).mono (by simp), fun q hq => ?_, ?_⟩
  · rw [u₅.mem, hm₄, Blocks.writeW64_in _ _ _ hq, hv, xmask_byte, Blocks.byte_readW64 _ _ hq, Blocks.byte_readW64 _ _ hq]
  · rw [u₅.mem, hm₄]
    exact Blocks.frame_writeW (w := 64) _ _ _ (by decide)

/-- The masked XOR of `w` words from `src + D` into `dst`. -/
theorem xorWords_ok {dst src : Reg} (hd : dst ≠ .x13 ∧ dst ≠ .x14) (hs : src ≠ .x13 ∧ src ≠ .x14) {c : Prop}
    [Decidable c] (hm : s.gpr .x12 = if c then BitVec.allOnes 64 else 0) {D w : Nat} (hD : D % 8 = 0)
    (hf₁ : D + 8 * w ≤ 32768) (hf₂ : 8 * w ≤ 32768)
    (hsrc : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 D) (8 * w))
    (hdst : InRegions s.wr (s.gpr dst) (8 * w))
    (hdis : Region.Disjoint ⟨s.gpr dst, 8 * w⟩ ⟨s.gpr src + BitVec.ofNat 64 D, 8 * w⟩) :
    WP isa (.block ((List.range w).flatMap (xorWord dst src D))) s
      (fun s' => XorPost c s s' (s.gpr dst) (s.gpr src + BitVec.ofNat 64 D) (8 * w)) := by
  refine WP.mono (Blocks.wp_range_flatMap (P := fun j t => j ≤ w → XorPost c s t (s.gpr dst) (s.gpr src + BitVec.ofNat 64 D) (8 * j))
    w (fun _ => ⟨Keep.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩)
    fun j hj t ht => ?_) fun t h => h (Nat.le_refl _)
  have c₀ := ht (by omega_using [hj])
  have hdt : t.gpr dst = s.gpr dst := c₀.keep.get dst (by simp [hd.1, hd.2])
  have hst : t.gpr src = s.gpr src := c₀.keep.get src (by simp [hs.1, hs.2])
  refine WP.mono (xor8_ok (s := t) hd (c := c) (by rw [c₀.keep.get .x12, hm])
      ⟨by omega_using [hD], by omega_using [hf₁, hj]⟩ (by omega_using [hf₂, hj])
      (by rw [hst, c₀.keep.rd, c₀.keep.wr, ← Blocks.ofNat_add']; exact Blocks.inRegions_off hsrc (by omega_using [hj]))
      (by rw [hdt, c₀.keep.wr]
          have := Blocks.inRegions_off (k := 8 * j) (l := 8) (show InRegions s.wr (s.gpr dst + BitVec.ofNat 64 0) (8 * w) by
            simpa using hdst) (by omega_using [hj])
          rwa [Blocks.ofNat_add', Nat.zero_add] at this)) fun t' c' _ => ?_
  rw [hdt, hst, ← Blocks.ofNat_add'] at c'
  have := XorPost.trans c₀ c' (by
      rw [show 8 * j + 8 = 8 * (j + 1) by omega_using []]
      exact (hdis.sub_left (Region.sub_prefix (by omega_using [hj]))).sub_right (Region.sub_prefix (by omega_using [hj])))
    (by omega_using [hf₂, hj])
  rwa [show 8 * j + 8 = 8 * (j + 1) by omega_using []] at this

end

/-- The mask's value: `x ⊕ i = 0` iff `x = i`. -/
theorem xor_zero_iff {x i : Nat} (hx : x < 2 ^ 32) (hi : i < 2 ^ 32) :
    BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 i = 0 ↔ x = i := by
  constructor
  · intro h
    have e := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx]),
      Nat.mod_eq_of_lt (by omega_using [hi])] at e
  · intro h; rw [h]; exact BitVec.xor_self

theorem xor_lt {x i : Nat} (hx : x < 2 ^ 32) (hi : i < 2 ^ 32) :
    (BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 i).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx]),
    Nat.mod_eq_of_lt (by omega_using [hi])]
  have := Nat.xor_lt_two_pow hx hi
  omega_using [this]

/-- `captureSk k`: lane `k`'s message XORed into the `n` bytes at `AU`
(`x24`) if `C + k = idx` (`x11 = C`, `x21 = idx`). -/
theorem capture_ok (hz : Sz p) {S AU : Addr} {k C idx : Nat} {t : State} (hk : k < 4)
    (h19 : t.gpr .x19 = S) (h11 : t.gpr .x11 = BitVec.ofNat 64 C) (h21 : t.gpr .x21 = BitVec.ofNat 64 idx)
    (h24 : t.gpr .x24 = AU) (hC : C + 4 < 2 ^ 32) (hidx : idx < 2 ^ 32) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (hout : InRegions t.wr AU p.n)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩) :
    WP isa (.block (Impl.SlhDsa.AArch64.Fors.captureSk ⟨p.n, p.len⟩ k)) t fun t' =>
      Keep [.x12, .x13, .x14] t t' ∧
      (∀ j < p.n, t'.mem (AU + BitVec.ofNat 64 j) =
        (if C + k = idx then t.mem (at' S (Layout.laneA k + p.n + 32) + BitVec.ofNat 64 j) else 0) ^^^
          t.mem (AU + BitVec.ofNat 64 j)) ∧
      Frame [⟨AU, p.n⟩] t.mem t'.mem := by
  have hn32 := hz.n32
  have e8 : 8 * (p.n / 8) = p.n := by have := hz.n8; omega_using [this]
  have hla := laneA_eq k
  simp only [Impl.SlhDsa.AArch64.Fors.captureSk, List.cons_append, List.nil_append]
  refine wp_addi (by omega_using [hk]) fun t₁ u₁ => wp_eor fun t₂ u₂ => ?_
  have hx : t₂.gpr .x12 = BitVec.ofNat 64 (C + k) ^^^ BitVec.ofNat 64 idx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h11, h21, BitVec.ofNat_add_ofNat]
  refine maskZero_ok (by decide) (by rw [hx]; exact xor_lt (by omega_using [hC, hk]) hidx) fun t₃ o₃ e₃ => ?_
  have hm : t₃.gpr .x12 = if C + k = idx then BitVec.allOnes 64 else 0 := by
    rw [e₃, hx]
    by_cases h : C + k = idx
    · rw [ite_eq_left h, ite_eq_left ((xor_zero_iff (by omega_using [hC, hk]) hidx).mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun e => h ((xor_zero_iff (by omega_using [hC, hk]) hidx).mp e))]
  have k₃ : Keep [.x12, .x13] t t₃ := (((upK u₁).trans (upK u₂)).trans o₃.keep).mono (by simp)
  have hm₃ : t₃.mem = t.mem := by rw [o₃.mem, u₂.mem, u₁.mem]
  have g19 : t₃.gpr .x19 = S := by rw [k₃.get .x19, h19]
  have g24 : t₃.gpr .x24 = AU := by rw [k₃.get .x24, h24]
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [k₃.wr]; exact hw
  refine WP.mono (xorWords_ok (s := t₃) (dst := .x24) (src := .x19) (c := C + k = idx)
    (D := Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) (w := p.n / 8) (by decide) (by decide) hm
    (by simp only [Layout.msgOff]; rw [hla]; omega_using [hz.n8])
    (by simp only [Layout.msgOff]; rw [hla]; omega_using [e8, hk, hn32]) (by omega_using [e8, hn32])
    (by rw [g19, e8]; exact in_scr' hw₃ (by simp only [Layout.msgOff]; rw [hla]; omega_using [hk, hn32]))
    (by rw [g24, e8, k₃.wr]; exact hout)
    (by rw [g24, g19, e8]; simp only [Layout.msgOff]
        rw [show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega_using []]; exact hd))
    fun t' c' => ?_
  rw [g24, g19, e8] at c'
  simp only [Layout.msgOff] at c'
  rw [show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega_using []] at c'
  exact ⟨(k₃.trans c'.keep).mono (by simp), fun j hj => by rw [c'.bytes j hj, hm₃], hm₃ ▸ c'.frame⟩

theorem zero_xor8 (x : Byte) : (0 : Byte) ^^^ x = x := BitVec.zero_xor

/-- The type fields of the lanes `A`. -/
abbrev typeRs (n : Nat) (S : Addr) : List Region :=
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + n + 16), 4⟩ : Region)

/-- What the second block of `leafBody` does: the private key value of the
index `idx`, if it is one of the leaves `C` to `C + 3` of the subtree,
XORed into the signature's at `AU`; the lanes' type `FORS_TREE`. -/
structure CapP (n : Nat) (S AU : Addr) (t t' : State) (C idx : Nat) : Prop where
  keep : Keep [.x9, .x11, .x12, .x13, .x14] t t'
  sk : ∀ j < n, t'.mem (AU + BitVec.ofNat 64 j) =
    if C ≤ idx ∧ idx < C + 4 then
      t.mem (at' S (Layout.laneA (idx - C) + n + 32) + BitVec.ofNat 64 j) ^^^ t.mem (AU + BitVec.ofNat 64 j)
    else t.mem (AU + BitVec.ofNat 64 j)
  ty : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + n + 16)) 4 = toByte 3 4
  frame : Frame (⟨AU, n⟩ :: typeRs n S) t.mem t'.mem

/-- A part of `scratch` below `oSigTmp` is apart from the signature. -/
theorem au_disj {S AU : Addr} {n o l : Nat} (hd : Region.Disjoint ⟨AU, n⟩ ⟨S, Layout.oSigTmp⟩)
    (h : o + l ≤ Layout.oSigTmp) : Region.Disjoint ⟨AU, n⟩ ⟨at' S o, l⟩ :=
  hd.sub_right (Offset.sub_base S h)

theorem capB_ok (hz : Sz p) {S AU : Addr} {U2 J idx : Nat} {t : State}
    (h19 : t.gpr .x19 = S) (h21 : t.gpr .x21 = BitVec.ofNat 64 idx) (h24 : t.gpr .x24 = AU)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 U2) (h26 : t.gpr .x26 = BitVec.ofNat 64 J)
    (hC : U2 + J + 4 < 2 ^ 32) (hidx : idx < 2 ^ 32) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (hout : InRegions t.wr AU p.n) (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) :
    WP isa (.block (([.add .x .x11 .x25 .x26] : List Instr) ++
        (List.range 4).flatMap (Impl.SlhDsa.AArch64.Fors.captureSk ⟨p.n, p.len⟩) ++
        (List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.setField .x19
          (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 3))) t
      fun t' => CapP p.n S AU t t' (U2 + J) idx := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eT : Layout.oSigTmp = 30144 := rfl
  simp only [List.singleton_append]
  refine wp_addr fun t₁ u₁ => ?_
  have hx₁ : t₁.gpr .x11 = BitVec.ofNat 64 (U2 + J) := by rw [u₁.gpr, h25, h26, BitVec.ofNat_add_ofNat]
  -- the captures
  refine WP.block_append (WP.mono (Blocks.wp_range_flatMap (P := fun K u => Keep [.x12, .x13, .x14] t₁ u ∧
      (∀ j < p.n, u.mem (AU + BitVec.ofNat 64 j) =
        if U2 + J ≤ idx ∧ idx < U2 + J + K then
          t.mem (at' S (Layout.laneA (idx - (U2 + J)) + p.n + 32) + BitVec.ofNat 64 j) ^^^ t.mem (AU + BitVec.ofNat 64 j)
        else t.mem (AU + BitVec.ofNat 64 j)) ∧
      Frame [⟨AU, p.n⟩] t.mem u.mem) 4
    ⟨Keep.refl _ _, fun j _ => by rw [ite_eq_right (by omega_using []), u₁.mem], by rw [u₁.mem]; exact Frame.refl _ _⟩
    fun K hK u ⟨ku, bu, fu⟩ => ?_) fun u hu => ?_) 
  · refine WP.mono (capture_ok hz (C := U2 + J) (idx := idx) hK (by rw [ku.get .x19, u₁.other _ (by decide), h19])
      (by rw [ku.get .x11, hx₁]) (by rw [ku.get .x21, u₁.other _ (by decide), h21])
      (by rw [ku.get .x24, u₁.other _ (by decide), h24]) hC hidx (by rw [ku.wr, u₁.wr]; exact hw)
      (by rw [ku.wr, u₁.wr]; exact hout) (au_disj hd (by rw [laneA_eq, eT]; omega_using [hK, hn32])))
      fun u' ⟨ku', bu', fu'⟩ => ⟨(ku.trans ku').mono (by simp), fun j hj => ?_, fu.trans fu'⟩
    have hl : u.mem (at' S (Layout.laneA K + p.n + 32) + BitVec.ofNat 64 j) =
        t.mem (at' S (Layout.laneA K + p.n + 32) + BitVec.ofNat 64 j) :=
      fu.bytes (R := ⟨at' S (Layout.laneA K + p.n + 32), p.n⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (au_disj hd (by rw [laneA_eq, eT]; omega_using [hK, hn32])).symm) (by show p.n ≤ 2 ^ 64; omega_using [hn32]) hj
    rw [bu' j hj, hl, bu j hj]
    by_cases h : U2 + J + K = idx
    · rw [ite_eq_left h, ite_eq_right (by omega_using [h]), ite_eq_left (by omega_using [h]),
        show idx - (U2 + J) = K by omega_using [h]]
    · rw [ite_eq_right h, zero_xor8]
      by_cases h' : U2 + J ≤ idx ∧ idx < U2 + J + K
      · rw [ite_eq_left h', ite_eq_left (by omega_using [h'])]
      · rw [ite_eq_right h', ite_eq_right (by omega_using [h, h'])]
  -- the types
  obtain ⟨ku, bu, fu⟩ := hu
  have g19 : u.gpr .x19 = S := by rw [ku.get .x19, u₁.other _ (by decide), h19]
  have hwu : (⟨S, 65536⟩ : Region) ∈ u.wr := by rw [ku.wr, u₁.wr]; exact hw
  have htd : ∀ r ∈ typeRs p.n S, Region.Disjoint ⟨AU, p.n⟩ r := fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact au_disj hd (by rw [laneA_eq, eT]; have := List.mem_range.mp hk; omega_using [this, hn32])
  refine WP.mono (Blocks.wp_range_flatMap (P := fun K v => Keep [.x9] u v ∧
      (∀ k < K, bytesAt v.mem (at' S (Layout.laneA k + p.n + 16)) 4 = toByte 3 4) ∧
      Frame (typeRs p.n S) u.mem v.mem) 4 ⟨Keep.refl _ _, fun _ h => absurd h (by omega_using []), Frame.refl _ _⟩
    fun K hK v ⟨kv, bv, fv⟩ => ?_) fun v ⟨kv, bv, fv⟩ => ?_
  · have hb : v.gpr .x19 = S := by rw [kv.get .x19, g19]
    rw [← List.append_nil (Impl.SlhDsa.AArch64.setField _ _ _)]
    simp only [Layout.adrsOff]
    refine setField_ok (by decide) ⟨by rw [laneA_eq]; omega_using [hn8], by rw [laneA_eq]; omega_using [hK, hn32]⟩
      (by rw [hb, kv.wr]; exact in_scr hwu (by rw [laneA_eq]; omega_using [hK, hn32])) fun v' f' => WP.block_nil ?_
    rw [hb] at f'
    have hf' : Frame [⟨at' S (Layout.laneA K + p.n + 16), 4⟩] v.mem v'.mem := f'.frame
    refine ⟨(kv.trans f'.keep).mono (by simp), fun k hk => ?_, fv.trans (hf'.sub fun r hr => ?_)⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact disj_scr S (by rw [laneA_eq, laneA_eq]; omega_using [hk']) (by rw [laneA_eq]; omega_using [hk', hK, hn32])
            (by rw [laneA_eq]; omega_using [hK, hn32])) (by decide), bv k hk']
      · exact f'.bytes
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨K, List.mem_range.mpr hK, rfl⟩, fun _ h => h⟩
  · refine ⟨(((upK u₁).trans ku).trans kv).mono (by simp), fun j hj => ?_, bv, ?_⟩
    · rw [fv.bytes (R := ⟨AU, p.n⟩) (fun r hr => htd r hr) (by show p.n ≤ 2 ^ 64; omega_using [hn32]) hj, bu j hj]
    · refine (fu.sub fun r hr => ?_).trans (fv.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, fun _ h => h⟩

/-! ## The leaves to the nodes -/

/-- What the last block of `leafBody` does: the four outputs to the nodes `J`
to `J + 3`, `x26 = J + 4`, and `x9 = J + 4 - P`. -/
structure OutP (n : Nat) (S : Addr) (t t' : State) (J P : Nat) : Prop where
  keep : Keep [.x9, .x10, .x11, .x14, .x26] t t'
  x26 : t'.gpr .x26 = BitVec.ofNat 64 (J + 4)
  x9 : t'.gpr .x9 = BitVec.ofNat 64 (J + 4) - BitVec.ofNat 64 P
  out : ∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (J + k) * n)) n = bytesAt t.mem (at' S (Layout.laneA k + n + 32)) n
  frame : Frame [⟨at' S (Layout.oN + J * n), 4 * n⟩] t.mem t'.mem

theorem out_ok (hz : Sz p) {S : Addr} {J P : Nat} {t : State} (h19 : t.gpr .x19 = S)
    (h26 : t.gpr .x26 = BitVec.ofNat 64 J) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    (hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots) (hP : P < 4096) :
    WP isa (.block (([Impl.SlhDsa.AArch64.Thash4.mov .x10 .x26] : List Instr) ++
        Impl.SlhDsa.AArch64.mulN (⟨p.n, p.len⟩ : Layout).n .x10 .x11 ++ ([.add .x .x10 .x10 .x19] : List Instr) ++
        (List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.copyWords .x10 (Layout.oN + (⟨p.n, p.len⟩ : Layout).n * k)
          .x19 (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) ((⟨p.n, p.len⟩ : Layout).n / 8)) ++
        ([.addImm .x .x26 .x26 4, .subImm .x .x9 .x26 P] : List Instr))) t
      fun t' => OutP p.n S t t' J P := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn8]
  have eN : Layout.oN = 12480 := rfl
  have eNS : Layout.nodeSlots = 520 := rfl
  rw [eNS, Nat.add_mul] at hJ
  simp only [Impl.SlhDsa.AArch64.Thash4.mov, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun t₁ u₁ => mulN_ok hz.nv (by decide) fun t₂ o₂ e₂ => wp_addr fun t₃ u₃ => ?_
  have k₃ : Keep [.x10, .x11] t t₃ := (((upK u₁).trans o₂.keep).trans (upK u₃)).mono (by simp)
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, o₂.mem, u₁.mem]
  have hx₃ : t₃.gpr .x10 = at' S (J * p.n) := by
    rw [u₃.gpr, e₂, u₁.gpr, o₂.get .x19, u₁.other _ (by decide), h19, h26, BitVec.ofNat_mul_ofNat, at',
      BitVec.add_comm]
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [k₃.wr]; exact hw
  have hlane : ∀ k < 4, Region.Disjoint ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩
      ⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩ := fun k hk =>
    disj_scr S (by rw [laneA_eq, eN]; omega_using [hk, hn32]) (by rw [laneA_eq]; omega_using [hk, hn32])
      (by rw [eN]; omega_using [hJ])
  refine wp_flatRange (P := fun K u => Keep [.x10, .x11, .x14] t u ∧ u.gpr .x10 = at' S (J * p.n) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.oN + (J + k) * p.n)) p.n =
        bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n) ∧
      Frame [⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩] t.mem u.mem) 4
    ⟨k₃.mono (by simp), hx₃, fun _ h => absurd h (by omega_using []), by rw [hm₃]; exact Frame.refl _ _⟩
    (fun K hK u is' ⟨ku, xu, bu, fu⟩ kk => ?_) fun u ⟨ku, xu, bu, fu⟩ => ?_
  · have g19 : u.gpr .x19 = S := by rw [ku.get .x19, h19]
    have hwu : (⟨S, 65536⟩ : Region) ∈ u.wr := by rw [ku.wr]; exact hw
    have hdst : u.gpr .x10 + BitVec.ofNat 64 (Layout.oN + p.n * K) = at' S (Layout.oN + (J + K) * p.n) := by
      rw [xu, at_add, show J * p.n + (Layout.oN + p.n * K) = Layout.oN + (J + K) * p.n by
        rw [Nat.add_mul, Nat.mul_comm p.n K]; omega_using []]
    have hnK : p.n * K + p.n ≤ 4 * p.n := by
      have := Nat.mul_le_mul_left p.n (show K + 1 ≤ 4 by omega_using [hK])
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.n 4] at this; exact this
    have hnK8 : p.n * K % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.zero_mul, Nat.zero_mod]
    have hfK : Layout.oN + (J + K) * p.n + p.n ≤ Layout.oN + J * p.n + 4 * p.n := by
      rw [Nat.add_mul, Nat.mul_comm K p.n]; omega_using [hnK]
    simp only [Layout.msgOff]
    refine copyWords_ok ⟨by decide, by decide, ⟨by rw [laneA_eq]; omega_using [hn8], by rw [laneA_eq]; omega_using [hK, hn32, e8]⟩,
      ⟨by rw [eN]; omega_using [hnK8], by rw [eN]; omega_using [hnK, hn32, e8]⟩,
      by rw [g19, e8]; exact in_scr' hwu (by rw [laneA_eq]; omega_using [hK, hn32]),
      by rw [hdst, e8]; exact in_scr hwu (by rw [eN] at hfK ⊢; omega_using [hfK, hJ]),
      by rw [hdst, g19, e8]
         exact disj_scr S (by rw [laneA_eq, eN]; omega_using [hK, hn32]) (by rw [eN] at hfK ⊢; omega_using [hfK, hJ])
           (by rw [laneA_eq]; omega_using [hK, hn32])⟩ fun u' k' f' c' => kk u' ?_
    rw [hdst, e8] at f' c'
    rw [g19, show Layout.laneA K + (p.n + 32) = Layout.laneA K + p.n + 32 by omega_using []] at c'
    have hsub : Frame [⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩] u.mem u'.mem := f'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by rw [Nat.add_mul]; omega_using []) hfK⟩
    refine ⟨(ku.trans k').mono (by simp), by rw [k'.get .x10, xu], fun k hk => ?_, fu.trans hsub⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · rw [bytesAt_frame f' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := Nat.mul_le_mul_right p.n (show k + 1 ≤ K by omega_using [hk'])
        rw [Nat.add_mul, Nat.one_mul] at this
        have h2 : (J + k) * p.n + p.n ≤ (J + K) * p.n := by rw [Nat.add_mul, Nat.add_mul]; omega_using [this]
        exact disj_scr S (by omega_using [h2]) (by rw [eN] at hfK ⊢; omega_using [hfK, hJ, h2])
          (by rw [eN] at hfK ⊢; omega_using [hfK, hJ])) (by omega_using [hn32]), bu k hk']
    · rw [c', bytesAt_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hlane k hK) (by omega_using [hn32])]
  · refine wp_addi (by decide) fun t₄ u₄ => wp_subi hP fun t₅ u₅ => WP.block_nil ?_
    have h26u : t₄.gpr .x26 = BitVec.ofNat 64 (J + 4) := by
      rw [u₄.gpr, ku.get .x26, h26, BitVec.ofNat_add_ofNat]
    refine ⟨((ku.trans (upK u₄)).trans (upK u₅)).mono (by simp), by rw [u₅.other _ (by decide), h26u],
      by rw [u₅.gpr, h26u], fun k hk => by rw [u₅.mem, u₄.mem]; exact bu k hk, by rw [u₅.mem, u₄.mem]; exact fu⟩

end VG.Proof.SlhDsa.AArch64.Fors
