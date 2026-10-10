import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Impl.AesGcm.X86_64.SealGather

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: copying a slice

Untrusted: everything here is checked by Lean. `copy` copies `rcx` bytes
from `rsi` to `rdi` (`copy_ok`), 64 at a time through `xmm0`–`xmm3`
(`copy64Step_ok`), then 16 at a time through `xmm0` (`copy16Step_ok`), then
the rest with the last 16 bytes, again through `xmm0`, if there are 16
(`copyLast_ok`), and otherwise one at a time (`copy1Step_ok`), with the index
in `r10`, and leaves what
ChaCha20-Poly1305's `copyBytes` leaves (`Gather.CopyPost`); the buffers do
not overlap. Each loop runs from one multiple of its step to another
(`chunks_wp`), with the first `j` bytes copied (`CInv`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather VG.WriteBytes
open VG.Proof.AesGcm.X86_64 (ea_idx succ_ofNat in_of_covers length_bytesAt bytesAt_add ofNat_add_ofNat bytesAt_frame
  imm_eq offset_nat sub_beq src_kept bytesAt_succ toNat_ofNat_of_lt)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (CopyPost)
open VG.Proof.AesGcm.X86_64.Short (writeW_readW128 CopyPre in_of_covers16 shl_ofNat)
open VG.Spec.Aes (bytesAt)

/-! ## A loop over chunks -/

/-- A loop whose body takes `P j` to `P (j + c)`, setting `ZF` when `j + c`
reaches `b`, from `j₀ < b` with `b - j₀` a multiple of `c`: `P b`. -/
theorem chunks_wp {body : List Instr} {c b : Nat} {P : Nat → State → Prop}
    (hstep : ∀ j t, P j t → j + c ≤ b →
      ∃ t', runBlock isa body t = some t' ∧ P (j + c) t' ∧ t'.zf = some (decide (j + c = b)))
    (hc : 0 < c) {j₀ : Nat} {t₀ : State} (h₀ : P j₀ t₀) (hlt : j₀ < b) (hdvd : (b - j₀) % c = 0) :
    WP isa (.loop (.block body) .ne) t₀ (P b) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = b - j ∧ j < b ∧ (b - j) % c = 0 ∧ P j t) ?_ (b - j₀) _
    ⟨j₀, rfl, hlt, hdvd, h₀⟩
  rintro k t ⟨j, rfl, hj, hd, hP⟩
  have hjc : j + c ≤ b := by
    rcases Nat.lt_or_ge (b - j) c with h | h
    · rw [Nat.mod_eq_of_lt h] at hd; omega
    · omega
  obtain ⟨t', run', hP', hz⟩ := hstep j t hP hjc
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have ev : isa.eval .ne t' = some !decide (j + c = b) := by show t'.zf.map (!·) = _; rw [hz]; rfl
  by_cases he : j + c = b
  · left
    exact ⟨by rw [ev]; simp [he], he ▸ hP'⟩
  · right
    refine ⟨by rw [ev]; simp [he], b - (j + c), by omega, j + c, rfl, by omega, ?_, hP'⟩
    rw [show b - (j + c) = (b - j) - c by omega]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hd) (Nat.dvd_refl c))

/-! ## The bodies -/

/-- Writing `ys` over `xs`, from the same address, when `ys` is as long. -/
theorem writeBytes_over (m : Mem) (q : Addr) {xs ys : List Byte} (h : xs.length ≤ ys.length) :
    writeBytes (writeBytes m q xs) q ys = writeBytes m q ys := by
  funext a
  simp only [writeBytes]
  by_cases h₁ : (a - q).toNat < ys.length
  · simp only [h₁, ite_true]
  · simp only [h₁, ite_false, show ¬ (a - q).toNat < xs.length by omega]

theorem ea_disp (s : State) (b : Reg) {B : Addr} (hb : s.gpr b = B) {j : Nat}
    (hi : s.gpr .r10 = BitVec.ofNat 64 j) (d : Nat) :
    s.gpr b + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (d : Int) = B + BitVec.ofNat 64 (j + d) := by
  rw [hb, hi, BitVec.mul_one, offset_nat, BitVec.add_assoc, ofNat_add_ofNat]

/-- Four 16-byte writes, one after the other, are one of 64 bytes. -/
theorem writeBytes_four (m src : Mem) (D S : Addr) (j : Nat) :
    writeBytes (writeBytes (writeBytes (writeBytes m (D + BitVec.ofNat 64 (j + 0))
        (bytesAt src (S + BitVec.ofNat 64 (j + 0)) 16)) (D + BitVec.ofNat 64 (j + 16))
        (bytesAt src (S + BitVec.ofNat 64 (j + 16)) 16)) (D + BitVec.ofNat 64 (j + 32))
        (bytesAt src (S + BitVec.ofNat 64 (j + 32)) 16)) (D + BitVec.ofNat 64 (j + 48))
        (bytesAt src (S + BitVec.ofNat 64 (j + 48)) 16) =
      writeBytes m (D + BitVec.ofNat 64 j) (bytesAt src (S + BitVec.ofNat 64 j) 64) := by
  have e : ∀ (P : Addr) (k : Nat), P + BitVec.ofNat 64 (j + k) = P + BitVec.ofNat 64 j + BitVec.ofNat 64 k :=
    fun P k => by rw [BitVec.add_assoc, ofNat_add_ofNat]
  rw [Nat.add_zero, Nat.add_zero, e D 16, e S 16, e D 32, e S 32, e D 48, e S 48]
  generalize D + BitVec.ofNat 64 j = D'
  generalize S + BitVec.ofNat 64 j = S'
  have a₁ := bytesAt_add src S' 16 48
  have a₂ := bytesAt_add src (S' + BitVec.ofNat 64 16) 16 32
  have a₃ := bytesAt_add src (S' + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) 16 16
  simp only [Nat.reduceAdd, Offset.add_add] at a₁ a₂ a₃
  rw [a₁, a₂, a₃, ← writeBytes_append _ _ _ _ (by simp [length_bytesAt]),
    ← writeBytes_append _ _ _ _ (by simp [length_bytesAt]), ← writeBytes_append _ _ _ _ (by simp [length_bytesAt])]
  simp only [List.length_append, length_bytesAt, Offset.add_add, Nat.reduceAdd]

/-- The first `j` bytes copied, the other registers but `rax`, `r8` and `r10`
kept. -/
structure CInv (s : State) (S D : Addr) (j : Nat) (t : State) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem D (bytesAt s.mem S j)
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

section
variable {s : State} {S D : Addr} {n : Nat} (h : CopyPre s S D n)
include h

/-- A block of the source, which the copy so far has left as it was. -/
theorem CInv.readW {j k : Nat} {t : State} (ht : CInv s S D j t) (hk : j + k + 16 ≤ n) :
    t.mem.readW (S + BitVec.ofNat 64 (j + k)) 128 = s.mem.readW (S + BitVec.ofNat 64 (j + k)) 128 := by
  have hn := h.lt
  refine Mem.readW_congr fun i hi => ?_
  rw [ht.mem]
  refine (writeBytes_frame s.mem D (bytesAt s.mem S j) (R := ⟨D, j⟩)
    (by rw [length_bytesAt]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Offset.add_add] at hcon
  exact h.disj _ (Offset.contains_base S (show j + k + i + 1 ≤ n by simp at hi; omega) (by omega))
    (Region.sub_prefix (show j ≤ n by omega) _ hcon)

/-- A block of the source anywhere in it, which the copy so far has left as
it was. -/
theorem CInv.readW' {j i : Nat} {t : State} (ht : CInv s S D j t) (hj : j ≤ n) (hi : i + 16 ≤ n) :
    t.mem.readW (S + BitVec.ofNat 64 i) 128 = s.mem.readW (S + BitVec.ofNat 64 i) 128 := by
  have hn := h.lt
  refine Mem.readW_congr fun k hk => ?_
  rw [ht.mem]
  refine (writeBytes_frame s.mem D (bytesAt s.mem S j) (R := ⟨D, j⟩)
    (by rw [length_bytesAt]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Offset.add_add] at hcon
  exact h.disj _ (Offset.contains_base S (show i + k + 1 ≤ n by simp at hk; omega) (by omega))
    (Region.sub_prefix hj _ hcon)

/-- `k` more bytes copied, from the source as it was. -/
theorem CInv.mem_add {j k : Nat} {t : State} (ht : CInv s S D j t) (hk : j + k ≤ n) {m : Mem}
    (hm : m = writeBytes t.mem (D + BitVec.ofNat 64 j) (bytesAt s.mem (S + BitVec.ofNat 64 j) k)) :
    m = writeBytes s.mem D (bytesAt s.mem S (j + k)) := by
  have hn := h.lt
  rw [hm, ht.mem, bytesAt_add]
  conv => lhs; rw [show D + BitVec.ofNat 64 j = D + BitVec.ofNat 64 (bytesAt s.mem S j).length by
    rw [length_bytesAt]]
  exact writeBytes_append _ _ _ _ (by rw [length_bytesAt, length_bytesAt]; omega)

theorem in_rd {j : Nat} {t : State} (ht : CInv s S D j t) {i k : Nat} (hik : i + k ≤ n) :
    InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 i) k := by
  have hn := h.lt
  rw [ht.rd, ht.wr]
  exact h.rd _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base S hik (by omega)⟩

theorem in_wr {j : Nat} {t : State} (ht : CInv s S D j t) {i k : Nat} (hik : i + k ≤ n) :
    InRegions t.wr (D + BitVec.ofNat 64 i) k := by
  have hn := h.lt
  rw [ht.wr]
  exact h.wr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hik (by omega)⟩

/-- The 64-byte loop's body. -/
theorem copy64Step_ok {j b : Nat} {t : State} (ht : CInv s S D j t) (hb : t.gpr .r8 = BitVec.ofNat 64 b)
    (hj : j + 64 ≤ n) (hbn : b ≤ n) :
    ∃ t', runBlock isa copy64Body t = some t' ∧ (CInv s S D (j + 64) t' ∧ t'.gpr .r8 = BitVec.ofNat 64 b) ∧
      t'.zf = some (decide (j + 64 = b)) := by
  have hn := h.lt
  have hs : t.gpr .rsi = S := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rsi]
  have hd : t.gpr .rdi = D := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rdi]
  have es := ea_disp t .rsi hs ht.r10
  have ed := ea_disp t .rdi hd ht.r10
  have r₀ := in_rd h ht (i := j + 0) (k := 16) (by omega)
  have r₁ := in_rd h ht (i := j + 16) (k := 16) (by omega)
  have r₂ := in_rd h ht (i := j + 32) (k := 16) (by omega)
  have r₃ := in_rd h ht (i := j + 48) (k := 16) (by omega)
  have w₀ := in_wr h ht (i := j + 0) (k := 16) (by omega)
  have w₁ := in_wr h ht (i := j + 16) (k := 16) (by omega)
  have w₂ := in_wr h ht (i := j + 32) (k := 16) (by omega)
  have w₃ := in_wr h ht (i := j + 48) (k := 16) (by omega)
  have i64 := imm_eq (n := 64) (by decide)
  refine ⟨_, by
    simp only [copy64Body, srcD, dstD]
    mrun [es, ed, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, i64], ?_⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, ht.r10, ofNat_add_ofNat]
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm', reduceCtorEq, ↓reduceIte]
    rw [ht.readW h (k := 0) (by omega), ht.readW h (k := 16) (by omega), ht.readW h (k := 32) (by omega),
      ht.readW h (k := 48) (by omega), writeW_readW128, writeW_readW128, writeW_readW128, writeW_readW128,
      writeBytes_four]
    exact ht.mem_add h hj rfl
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, c]; exact ht.keep r a b c
  · simp [rd_setReg, rd_arithFlags, rd_setXmm, ht.rd]
  · simp [wr_setReg, wr_arithFlags, wr_setXmm, ht.wr]
  · simp [gpr_setReg, gpr_arithFlags, hb]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte, ht.r10, hb]
    rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]

/-- The 16-byte loop's body. -/
theorem copy16Step_ok {j b : Nat} {t : State} (ht : CInv s S D j t) (hb : t.gpr .r8 = BitVec.ofNat 64 b)
    (hj : j + 16 ≤ n) (hbn : b ≤ n) :
    ∃ t', runBlock isa copy16Body t = some t' ∧ (CInv s S D (j + 16) t' ∧ t'.gpr .r8 = BitVec.ofNat 64 b) ∧
      t'.zf = some (decide (j + 16 = b)) := by
  have hn := h.lt
  have hs : t.gpr .rsi = S := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rsi]
  have hd : t.gpr .rdi = D := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rdi]
  have es := ea_disp t .rsi hs ht.r10
  have ed := ea_disp t .rdi hd ht.r10
  have r₀ := in_rd h ht (i := j + 0) (k := 16) (by omega)
  have w₀ := in_wr h ht (i := j + 0) (k := 16) (by omega)
  have i16 := imm_eq (n := 16) (by decide)
  refine ⟨_, by
    simp only [copy16Body, srcD, dstD]
    mrun [es, ed, r₀, w₀, i16], ?_⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, ht.r10, ofNat_add_ofNat]
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm', reduceCtorEq, ↓reduceIte]
    rw [ht.readW h (k := 0) (by omega), writeW_readW128, Nat.add_zero]
    exact ht.mem_add h hj rfl
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, c]; exact ht.keep r a b c
  · simp [rd_setReg, rd_arithFlags, rd_setXmm, ht.rd]
  · simp [wr_setReg, wr_arithFlags, wr_setXmm, ht.wr]
  · simp [gpr_setReg, gpr_arithFlags, hb]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte, ht.r10, hb]
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]

/-- The byte loop's body. -/
theorem copy1Step_ok {j : Nat} {t : State} (ht : CInv s S D j t) (hj : j + 1 ≤ n) :
    ∃ t', runBlock isa copy1Body t = some t' ∧ CInv s S D (j + 1) t' ∧ t'.zf = some (decide (j + 1 = n)) := by
  have hn := h.lt
  have hs : t.gpr .rsi = S := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rsi]
  have hd : t.gpr .rdi = D := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rdi]
  have hc : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  have es := ea_disp t .rsi hs ht.r10 0
  have ed := ea_disp t .rdi hd ht.r10 0
  rw [Nat.add_zero] at es ed
  have r₀ := in_rd h ht (i := j) (k := 1) (by omega)
  have w₀ := in_wr h ht (i := j) (k := 1) (by omega)
  have i1 := imm_eq (n := 1) (by decide)
  refine ⟨_, by
    simp only [copy1Body, srcD, dstD]
    mrun [es, ed, r₀, w₀, i1], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, ht.r10, ofNat_add_ofNat]
  · have hlen : (bytesAt s.mem S j).length = j := length_bytesAt _ _ _
    simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
    rw [ht.mem, src_kept h.disj (by omega) h.lt _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S j) _ (by rw [hlen]; omega), hlen]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, c]; exact ht.keep r a b c
  · simp [rd_setReg, rd_arithFlags, ht.rd]
  · simp [wr_setReg, wr_arithFlags, ht.wr]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte, reduceCtorEq, ht.r10, hc]
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]

/-- The last 16 bytes, after `j ≥ n - 16` of them: all `n` copied. -/
theorem copyLast_ok {j : Nat} {t : State} (ht : CInv s S D j t) (hj : n - 16 ≤ j) (hjn : j ≤ n) (h16 : 16 ≤ n) :
    WP isa (.block copyLast) t (CopyPost s S D n) := by
  have hn := h.lt
  have hs : t.gpr .rsi = S := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rsi]
  have hd : t.gpr .rdi = D := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rdi]
  have hc : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 16 = BitVec.ofNat 64 (n - 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_of_lt (show n < 2 ^ 64 by omega), toNat_ofNat_of_lt (show 16 < 2 ^ 64 by decide),
      toNat_ofNat_of_lt (show n - 16 < 2 ^ 64 by omega)]
    omega
  have i16 := imm_eq (n := 16) (by decide)
  rw [show copyLast = [.mov .r10 (.reg .rcx), .alu .sub .r10 (imm 16)] ++
    ([.movdquLoad .xmm0 (srcD 0), .movdquStore (dstD 0) .xmm0] : List Instr) from rfl, WP.block_append_iff]
  obtain ⟨t₁, run₁, r10₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .r10 (.reg .rcx), .alu .sub .r10 (imm 16)] t =
      some t₁ ∧ t₁.gpr .r10 = BitVec.ofNat 64 (n - 16) ∧ (∀ r, r ≠ .r10 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by xrun [hc, i16, hsub], by simp [gpr_setReg, gpr_arithFlags, hc, i16, hsub],
      fun r hr => by simp [gpr_setReg, gpr_arithFlags, hr], by simp [mem_setReg, mem_arithFlags],
      by simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags]⟩
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  have es := ea_disp t₁ .rsi (by rw [g₁ _ (by decide), hs]) r10₁ 0
  have ed := ea_disp t₁ .rdi (by rw [g₁ _ (by decide), hd]) r10₁ 0
  rw [Nat.add_zero] at es ed
  have r₀ : InRegions (t₁.rd ++ t₁.wr) (S + BitVec.ofNat 64 (n - 16)) 16 := by
    rw [rd₁, wr₁]; exact in_rd h ht (by omega)
  have w₀ : InRegions t₁.wr (D + BitVec.ofNat 64 (n - 16)) 16 := by rw [wr₁]; exact in_wr h ht (by omega)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [srcD, dstD]
    mrun [es, ed, r₀, w₀], ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mem_setXmm, xmm_setXmm', ↓reduceIte, m₁]
    rw [ht.readW' h hjn (i := n - 16) (by omega), writeW_readW128, ht.mem]
    -- The first `j` bytes, then the last 16 over the `j - (n - 16)` of them before the rest.
    have a₁ := bytesAt_add s.mem S (n - 16) (j - (n - 16))
    have a₂ := bytesAt_add s.mem S (n - 16) 16
    rw [show n - 16 + (j - (n - 16)) = j by omega] at a₁
    rw [show n - 16 + 16 = n by omega] at a₂
    have hA : (bytesAt s.mem S (n - 16)).length = n - 16 := length_bytesAt _ _ _
    rw [a₁, ← writeBytes_append _ _ _ _ (by rw [length_bytesAt, length_bytesAt]; omega), hA,
      writeBytes_over _ _ (by rw [length_bytesAt, length_bytesAt]; omega),
      show D + BitVec.ofNat 64 (n - 16) = D + BitVec.ofNat 64 (bytesAt s.mem S (n - 16)).length by rw [hA],
      writeBytes_append _ _ _ _ (by rw [length_bytesAt, length_bytesAt]; omega), ← a₂]
  · intro r a b c; simp only [gpr_setXmm]; rw [g₁ r c]; exact ht.keep r a b c
  · simp [rd_setXmm, rd₁, ht.rd]
  · simp [wr_setXmm, wr₁, ht.wr]

end

theorem shr_ofNat (n k : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn),
    Nat.shiftRight_eq_div_pow]

/-- `r8 := c ⌊n / c⌋` for `c = 2 ^ k`, by shifts. -/
theorem round_ofNat (n k : Nat) (hn : n < 2 ^ 63) :
    BitVec.ofNat 64 n >>> k <<< k = BitVec.ofNat 64 (2 ^ k * (n / 2 ^ k)) := by
  rw [shr_ofNat n k (by omega), shl_ofNat (by
    have : n / 2 ^ k * 2 ^ k ≤ n := Nat.div_mul_le_self n _
    omega), Nat.mul_comm]

section
variable {s : State} {S D : Addr} {n : Nat} (h : CopyPre s S D n)
include h

/-- The first setup: none copied, `r8 = 64 ⌊n / 64⌋`, `ZF` if it is 0. -/
theorem setup64_ok : WP isa (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6, .shift .shl .r8 6,
      .alu .cmp .r8 (imm 0)]) s fun t => (CInv s S D 0 t ∧ t.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64))) ∧
      t.zf = some (decide (64 * (n / 64) = 0)) := by
  have hn := h.lt
  have e := round_ofNat n 6 hn
  simp only [Nat.reducePow] at e
  have i0 := imm_eq (n := 0) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, h.rcx, i0], ?_⟩
  refine ⟨⟨⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], by simp [bytesAt, writeBytes_nil, mem_setReg,
      mem_setFlags, mem_arithFlags], fun r a b c => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, b, c],
      by simp [rd_setReg, rd_setFlags, rd_arithFlags], by simp [wr_setReg, wr_setFlags, wr_arithFlags]⟩,
    by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, e]⟩, ?_⟩
  simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ↓reduceIte, e]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sub_beq (by omega) (by decide)]

/-- The second setup: `r8 = 16 ⌊n / 16⌋`, `ZF` if the first loop reached it. -/
theorem setup16_ok {t : State} (ht : CInv s S D (64 * (n / 64)) t) :
    WP isa (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4, .alu .cmp .r10 (.reg .r8)]) t
      fun u => (CInv s S D (64 * (n / 64)) u ∧ u.gpr .r8 = BitVec.ofNat 64 (16 * (n / 16))) ∧
        u.zf = some (decide (64 * (n / 64) = 16 * (n / 16))) := by
  have hn := h.lt
  have hc : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  have e := round_ofNat n 4 hn
  simp only [Nat.reducePow] at e
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, hc], ?_⟩
  refine ⟨⟨⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, ht.r10], by simp [mem_setReg, mem_setFlags,
      mem_arithFlags, ht.mem], fun r a b c => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, b]; exact ht.keep r a b c,
      by simp [rd_setReg, rd_setFlags, rd_arithFlags, ht.rd], by simp [wr_setReg, wr_setFlags, wr_arithFlags, ht.wr]⟩,
    by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, e]⟩, ?_⟩
  simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ↓reduceIte, reduceCtorEq, e, ht.r10]
  rw [sub_beq (by omega) (by omega)]

/-- The third setup: `ZF` if the second loop reached `n`. -/
theorem setup1_ok {t : State} (ht : CInv s S D (16 * (n / 16)) t) :
    WP isa (.block [.alu .cmp .r10 (.reg .rcx)]) t fun u => CInv s S D (16 * (n / 16)) u ∧
      u.zf = some (decide (16 * (n / 16) = n)) := by
  have hn := h.lt
  have hc : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  apply WP.of_runBlock
  refine ⟨_, by xrun [hc, ht.r10], ?_⟩
  refine ⟨⟨by simp [gpr_arithFlags, ht.r10], by simp [mem_arithFlags, ht.mem],
    fun r a b c => by simp [gpr_arithFlags]; exact ht.keep r a b c, by simp [rd_arithFlags, ht.rd],
    by simp [wr_arithFlags, ht.wr]⟩, ?_⟩
  simp only [zf_arithFlags]
  rw [sub_beq (by omega) (by omega)]

/-- The fourth setup: `CF` if there are fewer than 16 bytes. -/
theorem setupLast_ok {j : Nat} {t : State} (ht : CInv s S D j t) :
    WP isa (.block [.alu .cmp .rcx (imm 16)]) t fun u => CInv s S D j u ∧ u.cf = some (decide (n < 16)) := by
  have hn := h.lt
  have hc : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  have i16 := imm_eq (n := 16) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [hc, i16], ?_⟩
  refine ⟨⟨by simp [gpr_arithFlags, ht.r10], by simp [mem_arithFlags, ht.mem],
    fun r a b c => by simp [gpr_arithFlags]; exact ht.keep r a b c, by simp [rd_arithFlags, ht.rd],
    by simp [wr_arithFlags, ht.wr]⟩, ?_⟩
  simp only [cf_arithFlags, toNat_ofNat_of_lt (show n < 2 ^ 64 by omega), toNat_ofNat_of_lt (show 16 < 2 ^ 64 by decide)]

/-- `copy`: the `n` bytes at `S` copied to `D`. -/
theorem copy_ok : WP isa copy s (CopyPost s S D n) := by
  have hn := h.lt
  have done : ∀ {t : State}, CInv s S D n t → CopyPost s S D n t := fun ht => ⟨ht.mem, ht.keep, ht.rd, ht.wr⟩
  unfold copy
  refine WP.seq (WP.mono (setup64_ok h) fun t₁ ⟨⟨c₁, r8₁⟩, z₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := CInv s S D (64 * (n / 64))) ?_ fun t₂ c₂ => ?_)
  · refine WP.ite (decide (64 * (n / 64) = 0)) (by simp only [eval, z₁]) (fun e => ?_) (fun e => ?_)
    · exact WP.block_nil (by have : 64 * (n / 64) = 0 := by simpa using e
                             rw [this]; exact c₁)
    · have hp : 0 < 64 * (n / 64) := by simp at e; omega
      exact WP.mono (chunks_wp (P := fun j t => CInv s S D j t ∧ t.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64)))
        (fun j t ⟨c, r8⟩ hj => copy64Step_ok h c r8 (by omega) (by omega)) (by decide)
        (⟨c₁, r8₁⟩ : CInv s S D 0 t₁ ∧ _) hp (by omega)) fun _ h => h.1
  refine WP.seq (WP.mono (setup16_ok h c₂) fun t₃ ⟨⟨c₃, r8₃⟩, z₃⟩ => ?_)
  refine WP.seq (WP.mono (Q := CInv s S D (16 * (n / 16))) ?_ fun t₄ c₄ => ?_)
  · refine WP.ite (decide (64 * (n / 64) = 16 * (n / 16))) (by simp only [eval, z₃]) (fun e => ?_) (fun e => ?_)
    · exact WP.block_nil (by have : 64 * (n / 64) = 16 * (n / 16) := by simpa using e
                             rw [← this]; exact c₃)
    · have hp : 64 * (n / 64) < 16 * (n / 16) := by simp at e; omega
      exact WP.mono (chunks_wp (P := fun j t => CInv s S D j t ∧ t.gpr .r8 = BitVec.ofNat 64 (16 * (n / 16)))
        (fun j t ⟨c, r8⟩ hj => copy16Step_ok h c r8 (by omega) (by omega)) (by decide)
        (⟨c₃, r8₃⟩ : CInv s S D (64 * (n / 64)) t₃ ∧ _) hp (by omega)) fun _ h => h.1
  refine WP.seq (WP.mono (setup1_ok h c₄) fun t₅ ⟨c₅, z₅⟩ => ?_)
  refine WP.ite (decide (16 * (n / 16) = n)) (by simp only [eval, z₅]) (fun e => ?_) (fun e => ?_)
  · exact WP.block_nil (done (by have : 16 * (n / 16) = n := by simpa using e
                                 rw [← this]; exact c₅))
  have hp : 16 * (n / 16) < n := by simp at e; omega
  refine WP.seq (WP.mono (setupLast_ok h c₅) fun t₆ ⟨c₆, cf₆⟩ => ?_)
  refine WP.ite (decide (n < 16)) (by simp only [eval, cf₆]) (fun e₆ => ?_) (fun e₆ => ?_)
  · exact WP.mono (chunks_wp (P := fun j t => CInv s S D j t) (fun j t c hj => copy1Step_ok h c hj) (by decide)
      c₆ hp (by omega)) fun _ h => done h
  · have h16 : 16 ≤ n := by simpa using e₆
    exact copyLast_ok h c₆ (by omega) (by omega) h16

end

end VG.Proof.AesGcm.X86_64.Gather
