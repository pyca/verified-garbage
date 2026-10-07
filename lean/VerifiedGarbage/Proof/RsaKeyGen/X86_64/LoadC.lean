import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-!
# A candidate on x86-64: the candidate

`loadC` sets `w = out_len / 8` and the arrays' bases, loads the first
`out_len` octets of `rand` into `aN`, sets its two top bits and its low bit
(`wv_candidate`), and `used := out_len` (`loadC_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `loadC` changes. -/
def loadCRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (8 * kUsed, 8)]

/-- The head of `loadC`: `w`, the bases, and `rand` and `out_len` into `rsi`
and `rcx`. -/
theorem loadCHead_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot (k / 8) 8 ≤ Z) (hk : k < 2 ^ 31) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k)
    (hR : word s.mem B (8 * kRand) = rp) :
    WP isa (.block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++
      setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) s fun t =>
      t.gpr .rsi = rp ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot (k / 8) aN) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧ (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .r12] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot (k / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := k / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hst : InRegions s.wr (off B (8 * sW)) 8 := hs.st (by unfold sW; omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r12 = BitVec.ofNat 64 (k / 8) ∧ t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (k / 8))) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl kLen (by decide), hK, hst]
    have : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k / 8 < 2 ^ 64 by omega)]
    rw [this]; exact ⟨rfl, rfl⟩) rfl) fun t₁ ⟨⟨hcx, h12, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (setBases_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) := by
    rw [ho₂.word (by unfold sW sArr; omega) (by unfold sW; omega), hm₁, word_writeW_self]
  have hR₂ : word t₂.mem B (8 * kRand) = rp := by
    rw [ho₂.word (by unfold kRand sFn sArr; omega) (by unfold kRand sFn; omega), hm₁,
      (writeW_outside s.mem B _ (by unfold sW; omega)).word (by unfold sW kRand sFn; omega) (by unfold kRand sFn; omega), hR]
  have hs₂ := hs.congr (k₂.2.2.trans k₁.2.2)
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = rp ∧ t.gpr .rbx = off B (slot (k / 8) aN) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * kRand) (by unfold kRand sFn; omega),
      hs₂.ld (d := 8 * sArr aN) (by unfold sArr aN; omega), hR₂, hb₂ aN (by decide)]) rfl) fun t ⟨⟨hsi, hbx, hm⟩, k₃⟩ => ?_
  refine ⟨hsi, by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact hcx, hbx, by rw [hm]; exact hW₂,
    fun j hj => by rw [hm]; exact hb₂ j hj, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro x hx
  rw [hm, ho₂ x (hx (8 * sArr 0, 64) (by simp)), hm₁, writeW_outside s.mem B _ (by unfold sW; omega) x (hx (8 * sW, 8) (by simp))]

/-- The candidate's bits, and `used := out_len`. -/
theorem loadCBits_ok {s : State} {B : Addr} {Z w k : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hA : word s.mem B (8 * sArr aN) = off B (slot w aN)) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aN))),
      .movImm64 .rdx (BitVec.ofNat 64 (3 * 2 ^ 62)), .alu .or .rdx (.mem (ix .rbx .r12 (-8))),
      .store (ix .rbx .r12 (-8)) .rdx, .mov .rdx (.mem (at0 .rbx)), .alu .or .rdx (.imm 1), .store (at0 .rbx) .rdx,
      .mov .rax (.mem (hdr kLen)), .store (hdr kUsed) .rax]) s fun t =>
      wv t.mem B (slot w aN) w = Spec.RsaKeyGen.candidate (64 * w) (wv s.mem B (slot w aN) w) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧
      Frm B [(slot w aN, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.rax, .rdx, .rbx, .r12] s t := by
  have hn := hs.nowrap
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hU : 8 * kUsed + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  generalize ht : word s.mem B (slot w aN + 8 * (w - 1)) = top
  generalize hb : word s.mem B (slot w aN) = bot
  have hb₁ : word (s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)) B
      (slot w aN) = bot := by
    rw [← hb]; exact (writeW_outside _ _ _ (by omega)).word (by omega) (by omega)
  have hK₂ : ((s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)).writeW
      (off B (slot w aN)) (bot ||| 1)).readW (off B (8 * kLen)) 64 = BitVec.ofNat 64 k := by
    have hk8 := hdr_lt_slot w aN (show kLen < 32 by decide)
    rw [← hK]
    exact ((writeW_outside _ _ _ (by omega)).word (by omega) (by omega)).trans
      ((writeW_outside _ _ _ (by omega)).word (by omega) (by omega))
  refine WP.mono (WP.keep [.rax, .rdx, .rbx, .r12] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)).writeW
        (off B (slot w aN)) (bot ||| 1)).writeW (off B (8 * kUsed)) (BitVec.ofNat 64 k) ∧
      t.gpr .r12 = BitVec.ofNat 64 w) (by
    have e1 := addrm8 (b := off B (slot w aN)) (i := BitVec.ofNat 64 w) rfl rfl (show 1 ≤ w by omega)
    have e2 : off B (slot w aN) + BitVec.ofInt 64 0 = off B (slot w aN) := by
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hW, hA, ix, at0, e1, e2,
      hs.ld (d := slot w aN + 8 * (w - 1)) (by omega), hs.st (d := slot w aN + 8 * (w - 1)) (by omega),
      hs.ld (d := slot w aN) (by omega), hs.st (d := slot w aN) (by omega), ht, hb₁, sx1,
      hl kLen (by decide), hK₂, hs.st (d := 8 * kUsed) (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega)])
    rfl) fun t ⟨⟨hm, h12⟩, k⟩ => ⟨?_, ?_, ?_, h12, k⟩
  · rw [hm, (writeW_outside _ _ _ (by omega)).wv (Or.inr hU) (by omega)]
    refine wv_candidate hw ?_ ?_ ?_
    · rw [word_writeW_self, hb]
    · rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega), word_writeW_self, ht, BitVec.or_comm]
    · intro j h0 hj
      rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ _ _ (by omega)).word (by omega) (by omega)]
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega) x (hx (8 * kUsed, 8) (by simp)),
      writeW_outside _ B _ (by omega) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega),
      writeW_outside _ B _ (by omega) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega)]

/-- `loadC` but its last block: `w`, the bases, and the octets of `c`. -/
theorem loadCFront_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot (k / 8) 8 ≤ Z) (hk1 : 16 ≤ k) (hk : k < 2 ^ 31) (hk8 : k % 8 = 0)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = k) :
    WP isa (.seq (.block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++
      setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) loadBE) s fun t =>
      wv t.mem B (slot (k / 8) aN) (k / 8) = Spec.Rsa.os2ip bs ∧ Scr t B Z ∧ t.gpr .rdi = B ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧ (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      (∀ i, 16 ≤ i → i < 32 → word t.mem B (8 * i) = word s.mem B (8 * i)) ∧
      Frm B (loadCRanges (k / 8)) s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have hw8 : (k + 7) / 8 = k / 8 := by omega
  have sN := Nat.le_trans (slot_le (w := k / 8) (show aN < 8 by decide)) hZ
  have hsl : ∀ r ∈ loadCRanges (k / 8), r.1 + r.2 ≤ Z := by
    have := hdr_lt_slot (k / 8) aN (show kUsed < 32 by decide)
    have := hdr_lt_slot (k / 8) aN (show sW < 32 by decide)
    simp only [loadCRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sArr, sW, kUsed, sFn] at * <;> omega
  refine WP.seq (WP.mono (loadCHead_ok hs hdi hZ hk hK hR) fun t₁ ⟨hsi, hcx, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (loadCRanges (k / 8)) s.mem t₁.mem := hf₁.mono (by simp [loadCRanges])
  refine WP.mono (loadArr_ok (j := aN) hs₁ (by decide) (by rw [hw8]; exact hZ) (hsrc.congrK (InScr.of_frm hf₁' hsl) k₁)
    hbl (by omega) hk hsi hcx (by rw [hw8]; exact hbx)) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_
  rw [hw8] at hv₂ ha₂
  have hf₂ : Frm B (loadCRanges (k / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays ha₂ (fun _ hj => (List.mem_singleton.mp hj) ▸ by simp [loadCRanges]))
  refine ⟨hv₂, hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi),
    by rw [ha₂.hslot (by decide)]; exact hW₁, fun j hj => by rw [ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj,
    fun i h1 h2 => ?_, hf₂, (k₁.trans k₂).mono (by decide)⟩
  by_cases h3 : i = kUsed
  · subst h3; rw [ha₂.hslot (by decide)]
    exact hf₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr, kUsed, sFn] <;> omega) (by omega)
  refine hf₂.word_eq (fun r hr => ?_) (by omega)
  have := hdr_lt_slot (k / 8) aN (i := i) (by omega)
  simp only [loadCRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, kUsed, sFn] at * <;> omega

/-- `loadC`: `c` from the first `k` octets of `rand`. -/
theorem loadC_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot (k / 8) 8 ≤ Z) (hk1 : 16 ≤ k) (hk : k < 2 ^ 31) (hk8 : k % 8 = 0)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = k) :
    WP isa (seqs loadC) s fun t =>
      wv t.mem B (slot (k / 8) aN) (k / 8) = Spec.RsaKeyGen.candidate (8 * k) (Spec.Rsa.os2ip bs) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧ word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      Frm B (loadCRanges (k / 8)) s.mem t.mem ∧ t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 (k / 8) ∧
      Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  have sN := Nat.le_trans (slot_le (w := k / 8) (show aN < 8 by decide)) hZ
  unfold loadC
  simp only [seqs]
  refine WP.assoc (WP.seq (WP.mono (loadCFront_ok hs hdi hZ hk1 hk hk8 hK hR hsrc hbl)
    fun t₂ ⟨hv₂, hs₂, hdi₂, hW₂, hb₂, hhd, hf₂, k₂⟩ => ?_))
  refine WP.mono (loadCBits_ok (k := k) hs₂ hdi₂ hZ (by omega) (by omega) hW₂ (hb₂ aN (by decide))
    (by rw [hhd kLen (by decide) (by decide)]; exact hK)) fun t ⟨hc, hU, hf, h12, k₃⟩ => ?_
  have hw64 : 64 * (k / 8) = 8 * k := by omega
  refine ⟨by rw [hc, hv₂, hw64], hU, ?_, fun j hj => ?_, hf₂.trans (hf.mono (by simp [loadCRanges])),
    (k₃.gpr (by decide)).trans hdi₂, h12, (k₂.trans k₃).mono (by decide)⟩
  · have h1 := hdr_lt_slot (k / 8) aN (show sW < 32 by decide)
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h1
      · exact Or.inl (by unfold sW kUsed sFn; omega)) (by omega)]; exact hW₂
  · have h1 := hdr_lt_slot (k / 8) aN (show sArr j < 32 by unfold sArr; omega)
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h1
      · exact Or.inl (by unfold sArr kUsed sFn; omega)) (by omega)]; exact hb₂ j hj

end VG.Proof.RsaKeyGen.X86_64
