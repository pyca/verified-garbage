import VerifiedGarbage.Proof.Bignum.AArch64.PubR2

/-!
# RSA on AArch64: the setup

From a header holding `k` (slot `sK`): `w = ⌈k / 8⌉` and the arrays' bases
(`head_ok`); bytes outside the working space (`Src`) into an array
(`loadArr_ok`); and `pcLoad`, the modulus into array `aN` and `-m⁻¹` into
its slot (`pcLoad_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## `w` and the bases -/

theorem shr3_w (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- `head`: `w` into `x12` and its slot, and the arrays' bases. -/
theorem head_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) :
    WP isa (.block head) s fun t =>
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t := by
  have hn := hs.nowrap
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have eaN : aN = 0 := rfl
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  unfold head
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 ((k + 7) / 8))) ?_ (by decide) (by decide)
      (by decide +kernel))
    fun t₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  · brun [h0, hdr_enc (show sK < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs.ld (d := 8 * sK) (by omega), hs.st (d := 8 * sW) (by omega), hK, shr3_w k hk]
  have hs₁ := hs.congr k₁.wr
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr .x0 (by decide)).trans h0) h12 (by unfold sArr; omega))
    fun t ⟨hb, ho, k₂⟩ => ⟨(k₂.gpr .x12 (by decide)).trans h12, ?_, hb, ?_, (k₁.trans k₂).mono (by decide)⟩
  · rw [ho.word (by omega) (by omega), hm₁, word_writeW_self]
  · have hw₁ : Outside B (8 * sW) 8 s.mem t₁.mem := by rw [hm₁]; exact writeW_outside s.mem B _ (by omega)
    exact (Frm.of_outside hw₁ (by simp)).trans (Frm.of_outside ho (by simp))

/-! ## Byte strings outside the working space -/

/-- The bytes `bs` at `p`, readable, outside the working space. -/
structure Src (s : State) (B : Addr) (Z : Nat) (p : Addr) (bs : List Byte) : Prop where
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (p + BitVec.ofNat 64 i) = bs[i]
  out : ∀ i < bs.length, Z ≤ ofs B (p + BitVec.ofNat 64 i)

theorem Src.congr {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : InScr B Z s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm _ (h.out i hi)]; exact h.val i hi, h.out⟩

theorem Src.congrK {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} {rs : List Reg}
    (h : Src s B Z p bs) (hm : InScr B Z s.mem t.mem) (k : Keep rs s t) : Src t B Z p bs :=
  h.congr hm k.rd k.wr

theorem src_of_region {s : State} {B : Addr} {Z : Nat} {p : Addr} {len : Nat}
    (hr : (⟨p, len⟩ : Region) ∈ s.rd ++ s.wr) (hlen : len ≤ 2 ^ 64)
    (hd : (⟨p, len⟩ : Region).Disjoint ⟨B, Z⟩) : Src s B Z p (Spec.Rsa.bytesAt s.mem p len) := by
  have hl : (Spec.Rsa.bytesAt s.mem p len).length = len := by simp [Spec.Rsa.bytesAt]
  refine ⟨fun i hi => ⟨_, hr, contains_byte p (by omega) hlen⟩, fun i hi => ?_,
    fun i hi => out_scr hd (contains_byte p (by omega) hlen)⟩
  simp [Spec.Rsa.bytesAt]

/-- `loadBE` of bytes outside the working space into array `j`. -/
theorem loadArr_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : Scr s B Z)
    (hj : j < 8) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hsrc : Src s B Z p bs) (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (h1 : s.gpr .x1 = p) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B (slot ((k + 7) / 8) j)) :
    WP isa loadBE s fun t =>
      wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (loadBE_ok hs h1 h2 h8 hk hk1 hk' rfl (by omega) (fun i hi => hsrc.rd i (by omega))
    (fun i hi => hsrc.val i (by omega)) (fun i hi => Or.inr (by have := hsrc.out i (by omega); omega)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega), h3⟩

/-! ## `pcLoad` -/

/-- `pcLoad`'s first block: `head`, then `m`'s pointer, base and length. -/
theorem pcHead_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np) :
    WP isa (.block (head ++ ([ldh .x1 sN, ldh .x8 (sArr aN), ldh .x2 sK] : List Instr))) s fun t =>
      t.gpr .x1 = np ∧ t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x8 = off B (slot ((k + 7) / 8) aN) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x8, .x12] s t := by
  have hn := hs.nowrap
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have eaN : aN = 0 := rfl
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hs h0 hZ hk hK) fun t₁ ⟨_, hW₁, hb₁, hf₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  have hw₁ : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) → word t₁.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => hf₁.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> omega) (by omega)
  refine WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = np ∧ t.gpr .x2 = BitVec.ofNat 64 k ∧
      t.gpr .x8 = off B (slot ((k + 7) / 8) aN) ∧ t.mem = t₁.mem) (by
    brun [(k₁.gpr .x0 (by decide)).trans h0, hdr_enc (show sN < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hs₁.ld (d := 8 * sN) (by omega),
      hs₁.ld (d := 8 * sK) (by omega), hs₁.ld (d := 8 * sArr aN) (by omega),
      hw₁ sN (by omega), hw₁ sK (by omega), hN, hK, hb₁ aN (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h1, h2, h8', hm⟩, k₂⟩ => ?_
  exact ⟨h1, h2, h8', by rw [hm]; exact hW₁, fun j hj => by rw [hm]; exact hb₁ j hj,
    by rw [hm]; exact hf₁, (k₁.trans k₂).mono (by decide)⟩

/-- The load: `w`, the bases, `m`, and `-m⁻¹` for the odd `m`. -/
theorem pcLoad_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hnl : nb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs pcLoad) s fun t => ∃ minv, Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      ((word t.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have eaN : aN = 0 := rfl
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have hsl : ∀ r ∈ pcLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr =>
    Nat.le_trans (pcLoadRanges_le _ r hr) hZ
  unfold pcLoad
  refine WP.seq (WP.mono (pcHead_ok hs h0 hZ (by omega) hK hN)
    fun t₁ ⟨h1, h2, h8', hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have hf₁' : Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [pcLoadRanges])
  refine WP.seq (WP.mono (loadArr_ok hs₁ (by decide) hZ (hnb.congrK (InScr.of_frm hf₁' hsl) k₁) hnl (by omega)
    hk h1 h2 h8') fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have hf₂ : Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays1 ha₂ (by simp [pcLoadRanges]))
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0)
  have hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ha₂.hslot (by decide)]; exact hW₁
  have hodd₀ : (word t₂.mem B (slot ((k + 7) / 8) aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ (k + 7) / 8 by omega), Nat.mod_mod_of_dvd _ (by decide), hv₂, hodd]
  have h8₂ : t₂.gpr .x8 = off B (slot ((k + 7) / 8) aN) := (k₂.gpr .x8 (by decide)).trans h8'
  show WP isa (.block ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv])) t₂ _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = word t₂.mem B (slot ((k + 7) / 8) aN) ∧
      t.mem = t₂.mem) (by
    brun [h8₂, hs₂.ld (d := slot ((k + 7) / 8) aN) (by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h3₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [h3₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [h3₃] at hinv
  have hs₄ := (hs₂.congr k₃.wr).congr k₄.wr
  have h0₄ : t₄.gpr .x0 = B := (k₄.gpr .x0 (by decide)).trans ((k₃.gpr .x0 (by decide)).trans h0₂)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)) (by
    brun [h0₄, hdr_enc (show sMinv < 32 by decide), hs₄.st (d := 8 * sMinv) (by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₅⟩ => ?_
  have hm' : t.mem = t₂.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15) := by rw [hm, hm₄, hm₃]
  have hwo : Outside B (8 * sMinv) 8 t₂.mem t.mem := by rw [hm']; exact writeW_outside _ B _ (by omega)
  refine ⟨t₄.gpr .x15, ⟨hs₄.congr k₅.wr, (k₅.gpr .x0 (by decide)).trans h0₄, ⟨?_, ?_, fun j hj => ?_⟩⟩, ?_, ?_,
    hf₂.trans (Frm.of_outside hwo (by simp [pcLoadRanges])),
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [hwo.word (by omega) (by omega)]; exact hW₂
  · rw [hm', word_writeW_self]
  · rw [hwo.word (d := 8 * sArr j) (by unfold sArr sMinv; omega) (by unfold sArr; omega)]; exact hb₂ j hj
  · rw [hwo.wv (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega) (by omega)]
    exact hv₂
  · rw [hwo.word (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega) (by omega)]
    exact hinv

end VG.Proof.Bignum.AArch64
