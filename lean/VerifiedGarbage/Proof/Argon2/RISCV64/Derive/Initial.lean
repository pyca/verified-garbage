module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Calls
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Absorb
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame

/-!
# Argon2 on RISC-V: H₀

`HI s₀ data s`: the BLAKE2b state at `scratch` has absorbed `data`, whose
length is in the frame. `start_ok` absorbs the header, `absorb_ok` an
input with its length prefix, `finish_ok` writes the digest to H₀'s place in
the frame: `code_ok`, H₀ (`Spec.Argon2.initialHash`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_add wp_addi wp_li wp_ld)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Impl.Argon2.RISCV64.Derive (countOff ld st lda ldw argOff h0Off)

/-- H₀'s streaming state at `scratch`, with `data` absorbed. -/
structure HI (s₀ : State) (data : List Byte) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (scrP s₀) data
  cnt : lw s₀ s countOff = BitVec.ofNat 64 data.length
  len : data.length < 2 ^ 36

/-- The parameters are kept when the frame's variables are. -/
theorem Prm.of_lw {s₀ s t : State} (pr : Prm s₀ s)
    (h : ∀ d, 224 ≤ d → d + 8 ≤ 248 → lw s₀ t d = lw s₀ s d) : Prm s₀ t :=
  ⟨by rw [h _ (by decide) (by decide)]; exact pr.segLen,
    by rw [h _ (by decide) (by decide)]; exact pr.laneLen,
    by rw [h _ (by decide) (by decide)]; exact pr.stride⟩

/-- The bytes at `p`: a word, then the rest. -/
theorem bytes_word (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (4 + n) = Spec.Blake2.wordBytes (m.readW p 32) ++ bytesAt m (p + BitVec.ofNat 64 4) n := by
  rw [Proof.Blake2.bytesAt_add, Proof.Blake2.wordBytes_readW (w := 32) m p (.inl rfl)]

theorem variant_code {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) :
    (prm s₀).variant.code = (kindV s₀).toNat := by
  simp only [prm]
  rcases (by omega_arith : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h <;>
    simp [h, Spec.Argon2.Variant.code, Spec.Argon2.params]

theorem le32_lo (x : BitVec 64) : Spec.Argon2.le32 (x.setWidth 32).toNat = Spec.Blake2.wordBytes (x.setWidth 32) := by
  simp only [Spec.Argon2.le32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem le32_lo' {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    Spec.Argon2.le32 x.toNat = Spec.Blake2.wordBytes (x.setWidth 32) := by
  rw [← le32_lo]
  congr 1
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem lo_lo (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem header_eq : Impl.Argon2.RISCV64.Derive.header =
    [ldw .a0 7, .store .w .a0 .s4 896,
     ldw .a0 17, .store .w .a0 .s4 900,
     ldw .a0 6, .store .w .a0 .s4 904,
     ldw .a0 5, .store .w .a0 .s4 908,
     .li .a0 0x13, .store .w .a0 .s4 912,
     ldw .a0 0, .store .w .a0 .s4 916] := rfl

/-- A word of `scratch` is kept by a store to another one. -/
theorem scr_keep {s₀ : State} {m m' : Mem} {o o' : Nat} (ho : o + 4 ≤ 16384) (ho' : o' + 4 ≤ 16384)
    (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o', 4⟩] m m') :
    m'.readW (scrP s₀ + BitVec.ofNat 64 o) 32 = m.readW (scrP s₀ + BitVec.ofNat 64 o) 32 := by
  refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ hd (by omega_arith) (by omega_arith)

/-- A store to `scratch` from offset 192 on keeps the streaming state. -/
theorem repr_store {s₀ : State} {m m' : Mem} {o n : Nat} (ho : 192 ≤ o) (ho' : o + n ≤ 16384)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, n⟩] m m') {data : List Byte}
    (h : Repr b (Spec.Blake2.init b 64 0) m (scrP s₀) data) :
    Repr b (Spec.Blake2.init b 64 0) m' (scrP s₀) data :=
  repr_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ ho (by omega_arith)) h

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The six header words, at `scratch + 896`. -/
theorem header_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (scrP s₀) []) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.header) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀) [] ∧
      bytesAt t.mem (scrP s₀ + BitVec.ofNat 64 896) 24 = Proof.Argon2.initialHeader (prm s₀) ∧
      ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d := by
  rw [header_eq]
  refine wp_ldw hp h (i := 7) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine wp_stscrw hp i₁ (o := 896) (by decide) (by decide) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine wp_ldw hp i₂ (i := 17) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  refine wp_stscrw hp i₃ (o := 900) (by decide) (by decide) (by decide) fun s₄ i₄ m₄ g₄ l₄ f₄ => ?_
  refine wp_ldw hp i₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅
  refine wp_stscrw hp i₅ (o := 904) (by decide) (by decide) (by decide) fun s₆ i₆ m₆ g₆ l₆ f₆ => ?_
  refine wp_ldw hp i₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  have i₇ := i₆.upd u₇
  refine wp_stscrw hp i₇ (o := 908) (by decide) (by decide) (by decide) fun s₈ i₈ m₈ g₈ l₈ f₈ => ?_
  refine wp_li (by decide) fun s₉ u₉ => ?_
  have i₉ := i₈.upd u₉
  refine wp_stscrw hp i₉ (o := 912) (by decide) (by decide) (by decide) fun s₁₀ i₁₀ m₁₀ g₁₀ l₁₀ f₁₀ => ?_
  refine wp_ldw hp i₁₀ (i := 0) (by decide) fun s₁₁ u₁₁ => ?_
  have i₁₁ := i₁₀.upd u₁₁
  refine wp_stscrw hp i₁₁ (o := 916) (by decide) (by decide) (by decide) fun t it mt gt lt ft => WP.block_nil ?_
  have L : ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d := fun d h₂ => by
    rw [lt d h₂, lw_mem u₁₁.mem, l₁₀ d h₂, lw_mem u₉.mem, l₈ d h₂, lw_mem u₇.mem,
      l₆ d h₂, lw_mem u₅.mem, l₄ d h₂, lw_mem u₃.mem, l₂ d h₂, lw_mem u₁.mem]
  have R : Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀) [] := by
    refine repr_store (by decide) (by decide) ft ?_
    rw [u₁₁.mem]; refine repr_store (by decide) (by decide) f₁₀ ?_
    rw [u₉.mem]; refine repr_store (by decide) (by decide) f₈ ?_
    rw [u₇.mem]; refine repr_store (by decide) (by decide) f₆ ?_
    rw [u₅.mem]; refine repr_store (by decide) (by decide) f₄ ?_
    rw [u₃.mem]; refine repr_store (by decide) (by decide) f₂ ?_
    rw [u₁.mem]; exact repr
  refine ⟨it, Prm.of_lw pr fun d _ h₂ => L d (by omega_arith), R, ?_, L⟩
  have w0 : t.mem.readW (scrP s₀ + BitVec.ofNat 64 896) 32 = arg32 s₀ 7 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem,
      scr_keep (by decide) (by decide) (by decide) f₄, u₃.mem, m₂, Mem.readW_writeW_self32, u₁.gpr, lo_lo]
  have w1 : t.mem.readW (scrP s₀ + BitVec.ofNat 64 900) 32 = (arg s₀ 17).setWidth 32 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem, m₄, Mem.readW_writeW_self32, u₃.gpr, lo_lo]
  have w2 : t.mem.readW (scrP s₀ + BitVec.ofNat 64 904) 32 = arg32 s₀ 6 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem, m₆, Mem.readW_writeW_self32, u₅.gpr, lo_lo]
  have w3 : t.mem.readW (scrP s₀ + BitVec.ofNat 64 908) 32 = arg32 s₀ 5 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem, m₈, Mem.readW_writeW_self32, u₇.gpr, lo_lo]
  have w4 : t.mem.readW (scrP s₀ + BitVec.ofNat 64 912) 32 = 0x13 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem, m₁₀, Mem.readW_writeW_self32, u₉.gpr]
    rfl
  have w5 : t.mem.readW (scrP s₀ + BitVec.ofNat 64 916) 32 = arg32 s₀ 0 := by
    rw [mt, Mem.readW_writeW_self32, u₁₁.gpr, lo_lo]
  have step : ∀ o, scrP s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 4 =
      scrP s₀ + BitVec.ofNat 64 (o + 4) := fun o => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show (24 : Nat) = 4 + 20 from rfl, bytes_word, step, show (20 : Nat) = 4 + 16 from rfl,
    bytes_word, step, show (16 : Nat) = 4 + 12 from rfl, bytes_word, step,
    show (12 : Nat) = 4 + 8 from rfl, bytes_word, step, show (8 : Nat) = 4 + 4 from rfl, bytes_word,
    step, show (4 : Nat) = 4 + 0 from rfl, bytes_word]
  simp only [Nat.reduceAdd]
  rw [w0, w1, w2, w3, w4, w5]
  have vc := variant_code hp.kind_le
  simp only [prm] at vc
  simp only [Proof.Argon2.initialHeader, prm, vc, List.append_assoc]
  simp only [Spec.Argon2.params, Spec.Argon2.le32, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    bytesAt, List.range_zero, List.map_nil, List.append_nil]
  rfl

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A call of the streaming functions keeps `HI`'s invariant, parameters
and count. -/
theorem Inv.keepsP {s t : State} (h : Inv s₀ s) (pr : Prm s₀ s) (k : HPrime.Keeps s t) :
    Inv s₀ t ∧ Prm s₀ t ∧ ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d :=
  let ⟨i, l⟩ := h.keeps hp k
  ⟨i, Prm.of_lw pr fun d _ h₂ => l d (by omega_arith), l⟩

/-- `start`: an unkeyed 64-byte hash of the header, whose length is the count. -/
theorem start_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.RISCV64.Derive.start s (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  unfold Impl.Argon2.RISCV64.Derive.start
  have A : WP isa (.block [.li .a1 64]) s fun t =>
      Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .a1 = BitVec.ofNat 64 64 :=
    wp_li (by decide) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁,
      Prm.of_lw pr fun d _ _ => lw_mem u₁.mem d, u₁.gpr⟩
  refine WP.seq (A.mono fun s₁ ⟨i₁, p₁, r₁⟩ => ?_)
  have hr31 := i₁.s4
  refine WP.seq ((HPrime.init_ok s₁ (by rw [r₁]; decide) (i₁.scr_in hp)).mono
    fun s₂ ⟨rp₂, g₂, rd₂, wr₂, sp₂, f₂⟩ => ?_)
  obtain ⟨i₂, p₂, -⟩ := i₁.keepsP hp p₁ ⟨g₂, rd₂, wr₂, sp₂, HPrime.init_frame _ f₂⟩
  rw [r₁, hr31] at rp₂
  refine WP.seq ((header_ok hp i₂ p₂ (by simpa using rp₂)).mono fun s₃ ⟨i₃, p₃, rp₃, hd₃, _⟩ => ?_)
  refine WP.seq ((HPrime.absorbFixed_ok s₃ (Spec.Blake2.init b 64 0) 896 24 (by decide) (by decide)
    (by decide) (by decide) (by rw [i₃.s4]; exact rp₃) (i₃.scr_in hp)).mono fun s₄ ⟨rp₄, k₄⟩ => ?_)
  obtain ⟨i₄, p₄, -⟩ := i₃.keepsP hp p₃ k₄
  rw [i₃.s4, hd₃] at rp₄
  refine wp_li (by decide) fun s₅ u₅ => ?_
  refine wp_stloc (i₄.upd u₅) (d := countOff) (by decide) fun t it vt ot _ mt => WP.block_nil ?_
  refine ⟨it, Prm.of_lw p₄ fun d _ h₂ => ?_, ?_, ?_, ?_⟩
  · rw [ot d (by omega_arith) (by simp only [countOff]; omega_arith), lw_mem u₅.mem]
  · rw [mt, u₅.mem]; exact repr_loc hp (by decide) _ rp₄
  · rw [vt, u₅.gpr, Proof.Argon2.initialHeader_length]
  · rw [Proof.Argon2.initialHeader_length]; decide

/-- `absorb`'s first block: LE32 of the length at `scratch + 920`, and
`update`'s arguments. -/
theorem absA_ok {len : Nat} (hlen : len < 18) {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa (.block [lda .a0 len, .store .w .a0 .s4 920, ld .a1 countOff, .addi .a2 .s4 920, .li .a3 4])
      s fun t => HI s₀ data t ∧ t.gpr .a1 = BitVec.ofNat 64 data.length ∧
        t.gpr .a2 = scrP s₀ + BitVec.ofNat 64 920 ∧ t.gpr .a3 = BitVec.ofNat 64 4 ∧
        bytesAt t.mem (scrP s₀ + BitVec.ofNat 64 920) 4 =
          Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32) := by
  refine wp_lda hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁
  refine wp_stscrw hp i₁ (o := 920) (by decide) (by decide) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine wp_ldloc i₂ (d := countOff) (by decide) fun s₃ u₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := ((i₂.upd u₃).upd u₄).upd u₅
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have L : ∀ d, d + 8 ≤ 320 → lw s₀ s₅ d = lw s₀ s d := fun d h₂ => by
    rw [lw_mem m₅, l₂ d h₂, lw_mem u₁.mem]
  refine ⟨⟨i₅, Prm.of_lw h.prm fun d _ h₂ => L d (by omega_arith),
    by rw [m₅]; exact repr_store (by decide) (by decide) f₂ (by rw [u₁.mem]; exact h.repr),
    by rw [L _ (by decide)]; exact h.cnt, h.len⟩, ?_, ?_, u₅.gpr, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, l₂ _ (by decide),
      lw_mem u₁.mem, h.cnt]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide),
      h.inv.s4]
  · rw [show (4 : Nat) = 4 + 0 from rfl, bytes_word, m₅, m₂, Mem.readW_writeW_self32, u₁.gpr]
    rfl

/-- `update` of `L` bytes at `D`, readable and outside `scratch` and the
in `scratch` from offset 768 on: the count is kept. -/
theorem absU_ok {data : List Byte} {s : State} (h : HI s₀ data s)
    (r4 : s.gpr .a1 = BitVec.ofNat 64 data.length) (hL : (s.gpr .a3).toNat < 2 ^ 32)
    (hdata : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨scrP s₀, 768⟩) :
    WP isa Impl.Argon2.RISCV64.HPrime.update s fun t =>
      Inv s₀ t ∧ Prm s₀ t ∧ lw s₀ t countOff = lw s₀ s countOff ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀)
        (data ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) := by
  have hl := h.len
  refine (HPrime.update_ok s (Spec.Blake2.init b 64 0) data (by rw [h.inv.s4]; exact h.repr) r4 (by omega_arith)
    (h.inv.scr_in hp) hdata (by rw [h.inv.s4]; exact dataState.sub_right (Region.sub_prefix (by decide)))
    (by rw [h.inv.s4]; exact dataState.sub_right (Offset.sub_base _ (by decide)))).mono
    fun t ⟨rp, g, rd, wr, sp, f⟩ => ?_
  obtain ⟨i, p, l⟩ := h.inv.keepsP hp h.prm ⟨g, rd, wr, sp, HPrime.update_frame _ f⟩
  rw [h.inv.s4] at rp
  exact ⟨i, p, l _ (by decide), rp⟩

/-- `absorb`'s second block: the count advanced by 4, and `update`'s
arguments. -/
theorem absB_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) {data : List Byte} {c : Nat}
    {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) (rp : Repr b (Spec.Blake2.init b 64 0) s.mem (scrP s₀) data)
    (hc : lw s₀ s countOff = BitVec.ofNat 64 c) :
    WP isa (.block [ld .a1 countOff, .addi .a1 .a1 4, st countOff .a1, lda .a2 ptr, lda .a3 len]) s
      fun t => Inv s₀ t ∧ Prm s₀ t ∧ Repr b (Spec.Blake2.init b 64 0) t.mem (scrP s₀) data ∧
        lw s₀ t countOff = BitVec.ofNat 64 (c + 4) ∧
        t.gpr .a1 = BitVec.ofNat 64 (c + 4) ∧ t.gpr .a2 = arg s₀ ptr ∧
        t.gpr .a3 = arg s₀ len := by
  refine wp_ldloc h (d := countOff) (by decide) fun s₁ u₁ => ?_
  refine wp_addi (by decide) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁).upd u₂
  have v₂ : s₂.gpr .a1 = BitVec.ofNat 64 (c + 4) := by
    rw [u₂.gpr, u₁.gpr, hc, BitVec.ofNat_add]
  refine wp_stloc i₂ (d := countOff) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_lda hp i₃ (i := ptr) hptr fun s₄ u₄ => wp_lda hp (i₃.upd u₄) (i := len) hlen
    fun s₅ u₅ => WP.block_nil ?_
  have m₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  refine ⟨(i₃.upd u₄).upd u₅, Prm.of_lw pr fun d _ h₂ => ?_, ?_, ?_, ?_, ?_, u₅.gpr⟩
  · rw [lw_mem m₅, o₃ d (by omega_arith) (by simp only [countOff]; omega_arith), lw_mem u₂.mem, lw_mem u₁.mem]
  · rw [m₅, m₃, u₂.mem, u₁.mem]; exact repr_loc hp (by decide) _ rp
  · rw [lw_mem m₅, v₃, v₂]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃, v₂]
  · rw [u₅.other _ (by decide), u₄.gpr]

/-- `absorb`'s last block: the count advanced by the input's length. -/
theorem absC_ok {len : Nat} (hlen : len < 18) {c : Nat} {s : State} (h : Inv s₀ s)
    (hc : lw s₀ s countOff = BitVec.ofNat 64 c) :
    WP isa (.block [ld .a1 countOff, lda .a0 len, .add .a1 .a1 .a0, st countOff .a1]) s fun t =>
      Inv s₀ t ∧ lw s₀ t countOff = BitVec.ofNat 64 (c + (arg s₀ len).toNat) ∧
      (∀ d, d + 8 ≤ 320 → (d + 8 ≤ countOff ∨ countOff + 8 ≤ d) → lw s₀ t d = lw s₀ s d) ∧
      Frame [⟨E s₀ + BitVec.ofNat 64 countOff, 8⟩] s.mem t.mem := by
  refine wp_ldloc h (d := countOff) (by decide) fun s₁ u₁ => ?_
  refine wp_lda hp (h.upd u₁) (i := len) hlen fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁).upd u₂).upd u₃
  refine wp_stloc i₃ (d := countOff) (by decide) fun t it vt ot _ mt => WP.block_nil
    ⟨it, ?_, fun d h₂ hd => ?_, ?_⟩
  · rw [vt, u₃.gpr, u₂.other _ (by decide), u₁.gpr, hc, u₂.gpr, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [ot d (by omega_arith) hd.symm, lw_mem u₃.mem, lw_mem u₂.mem,
      lw_mem u₁.mem]
  · rw [mt, u₃.mem, u₂.mem, u₁.mem]; exact frame_loc _

theorem absorb_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR : (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hl : (arg s₀ len).toNat < 2 ^ 32) {data : List Byte}
    (hd : data.length + 4 + 2 ^ 32 < 2 ^ 36) {s : State} (h : HI s₀ data s) :
    WP isa (Impl.Argon2.RISCV64.Derive.absorb ptr len) s
      (HI s₀ (Proof.Argon2.appendInput data (bytesAt s₀.mem (arg s₀ ptr) (arg s₀ len).toNat))) := by
  have hR' : (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have hS : (⟨arg s₀ ptr, (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.RISCV64.Derive.absorb
  refine WP.seq ((absA_ok hp hlen h).mono fun s₁ ⟨h₁, r4₁, r5₁, r6₁, w₁⟩ => ?_)
  refine WP.seq ((absU_ok hp h₁ r4₁ (by rw [r6₁]; decide)
    (by rw [r5₁, r6₁, h₁.inv.wr]
        exact VG.Covers.right (VG.Covers.one ⟨scrR s₀, scr_mem hp, Offset.contains_base _ (by decide) (by decide)⟩))
    (by rw [r5₁, r6₁]; exact Offset.disjoint_base _ (by decide) (by decide))).mono
    fun s₂ ⟨i₂, p₂, c₂, rp₂⟩ => ?_)
  rw [r5₁, r6₁, show (BitVec.ofNat 64 4).toNat = 4 from rfl, w₁] at rp₂
  have wl : (Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32)).length = 4 := by
    simp [Spec.Blake2.wordBytes]
  have dl : (data ++ Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32)).length = data.length + 4 := by
    rw [List.length_append, wl]
  refine WP.seq ((absB_ok hp hptr hlen i₂ p₂ rp₂ (c := data.length) (by rw [c₂, h₁.cnt])).mono
    fun s₃ ⟨i₃, p₃, rp₃, c₃, r4₃, r5₃, r6₃⟩ => ?_)
  refine WP.seq ((absU_ok hp ⟨i₃, p₃, rp₃, by rw [c₃, dl], by rw [dl]; omega_arith⟩ (by rw [r4₃, dl])
    (by rw [r6₃]; exact hl)
    (by rw [r5₃, r6₃, i₃.rd, hp.rd]
        exact VG.Covers.left (VG.Covers.one ⟨_, hR', Region.contains_self _ _⟩))
    (by rw [r5₃, r6₃]
        exact (hp.ro_w _ hR' (scrR s₀) (by simp)).sub_right (Region.sub_prefix (by decide)))).mono
    fun s₄ ⟨i₄, p₄, c₄, rp₄⟩ => ?_)
  rw [r5₃, r6₃, i₃.input hp (R := ⟨arg s₀ ptr, (arg s₀ len).toNat⟩) hR] at rp₄
  refine (absC_ok hp hlen i₄ (c := data.length + 4) (c₄.trans c₃)).mono fun t ⟨it, ct, lt, ft⟩ => ?_
  have hd' : Proof.Argon2.appendInput data (bytesAt s₀.mem (arg s₀ ptr) (arg s₀ len).toNat) =
      data ++ Spec.Blake2.wordBytes ((arg s₀ len).setWidth 32) ++
        bytesAt s₀.mem (arg s₀ ptr) (arg s₀ len).toNat := by
    simp only [Proof.Argon2.appendInput, bytesAt, List.length_map, List.length_range,
      le32_lo' hl]
  have hlen' : (Proof.Argon2.appendInput data (bytesAt s₀.mem (arg s₀ ptr) (arg s₀ len).toNat)).length =
      data.length + 4 + (arg s₀ len).toNat := by
    rw [Proof.Argon2.appendInput_length]; simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨it, Prm.of_lw p₄ fun d _ h₂ => lt d (by omega_arith) (by simp only [countOff]; omega_arith), ?_,
    by rw [hlen']; exact ct, by rw [hlen']; omega_arith⟩
  rw [hd']
  exact repr_frame ft (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := (loc_scr hp (d := countOff) (by decide) (o := 0) (n := 192) (by decide)).symm
    simpa using this) (by simpa only [List.append_assoc] using rp₄)

end

/-- The bytes of `8 k` bytes, from their doublewords. -/
theorem bytes_of_dwords {m m' : Mem} {p p' : Addr} {k : Nat}
    (h : ∀ j < k, m'.readW (p' + BitVec.ofNat 64 (8 * j)) 64 = m.readW (p + BitVec.ofNat 64 (8 * j)) 64) :
    bytesAt m' p' (8 * k) = bytesAt m p (8 * k) := by
  rw [Proof.Blake2.bytesAt_words (w := 64), Proof.Blake2.bytesAt_words (w := 64)]
  simp only [List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun j hj => ?_)
  rw [← Proof.Blake2.wordBytes_readW (w := 64) _ _ (.inr rfl),
    ← Proof.Blake2.wordBytes_readW (w := 64) _ _ (.inr rfl)]
  exact congrArg _ (h j (List.mem_range.mp hj))

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first `k` doublewords of the digest, copied to H₀'s place. -/
theorem copy_ok {s : State} (h : Inv s₀ s) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap Impl.Argon2.RISCV64.Derive.copyWord)) s fun t =>
      Inv s₀ t ∧
      (∀ j < k, lw s₀ t (8 * j) = s.mem.readW (scrP s₀ + BitVec.ofNat 64 (768 + 8 * j)) 64) ∧
      (∀ e, e + 8 ≤ 320 → 8 * k ≤ e → lw s₀ t e = lw s₀ s e) ∧
      Frame [inR s₀] s.mem t.mem
  | 0, _ => WP.block_nil ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Frame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((copy_ok h k (by omega_arith)).mono fun t ⟨it, wt, lt, ft⟩ => ?_)
    simp only [Impl.Argon2.RISCV64.Derive.copyWord, Impl.Argon2.RISCV64.Derive.h0Off, Nat.zero_add]
    refine wp_ld (a := scrP s₀ + BitVec.ofNat 64 (768 + 8 * k)) (by omega_arith) (by rw [it.s4])
      (it.scr_al (by decide) (by omega_arith)) (by
        rw [it.rd, it.wr]
        exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp),
          Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) fun t₁ u₁ => ?_
    have i₁ := it.upd u₁
    refine wp_stloc i₁ (d := 8 * k) ⟨.inl (by omega_arith), by omega_arith⟩
      fun t₂ i₂ v₂ o₂ _ m₂ => WP.block_nil ⟨i₂, fun j hj => ?_, fun e h₂ hke => ?_, ?_⟩
    · have sc : t.mem.readW (scrP s₀ + BitVec.ofNat 64 (768 + 8 * j)) 64 =
          s.mem.readW (scrP s₀ + BitVec.ofNat 64 (768 + 8 * j)) 64 :=
        ft.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ((stk_disj hp (d := 0) (n := 72) (by decide) (scrR s₀) (by simp)).symm.sub_left
            (scr_sub (by omega_arith)))) (by decide)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [o₂ _ (by omega_arith) (by omega_arith), lw_mem u₁.mem]; exact wt j hj
      · rw [v₂, u₁.gpr, sc]
    · rw [o₂ _ h₂ (by omega_arith), lw_mem u₁.mem]; exact lt e h₂ (by omega_arith)
    · rw [m₂, u₁.mem]
      refine ft.writeW (List.mem_singleton_self _) _ ?_
      exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- `finish`: the digest of `data`, at H₀'s place. -/
theorem finish_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa Impl.Argon2.RISCV64.Derive.finish s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (E s₀ + BitVec.ofNat 64 0) 64 =
        Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  have hl := h.len
  unfold Impl.Argon2.RISCV64.Derive.finish
  refine WP.seq (wp_ldloc h.inv (d := countOff) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  refine WP.seq ((HPrime.finalize_ok s₁ (Spec.Blake2.init b 64 0) data
    (by rw [(h.inv.upd u₁).s4, u₁.mem]; exact h.repr) (by rw [u₁.gpr, h.cnt]) (by omega_arith)
    ((h.inv.upd u₁).scr_in hp)).mono
    fun s₂ ⟨dg, g₂, rd₂, wr₂, sp₂, f₂⟩ => ?_)
  obtain ⟨i₂, p₂, -⟩ := (h.inv.upd u₁).keepsP hp (Prm.of_lw h.prm fun d _ _ => lw_mem u₁.mem d)
    ⟨g₂, rd₂, wr₂, sp₂, HPrime.finalize_frame _ f₂⟩
  rw [(h.inv.upd u₁).s4] at dg
  refine (copy_ok hp i₂ 8 (Nat.le_refl _)).mono fun t ⟨it, wt, lt, _⟩ =>
    ⟨it, Prm.of_lw p₂ fun d h₁ h₂ => lt d (by omega_arith) (by omega_arith), ?_⟩
  · rw [← dg]
    refine bytes_of_dwords (k := 8) fun j hj => ?_
    have := wt j hj
    simp only [lw] at this
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add, this, BitVec.add_assoc, show (768 : Addr) =
      BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add_ofNat]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem code_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.RISCV64.Derive.code s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (E s₀ + BitVec.ofNat 64 0) 64 =
        Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  have l1 : (arg s₀ 2).toNat < 2 ^ 32 := hp.valid.2.2.2.2.2.2.2.2.1
  have l2 : (arg s₀ 4).toNat < 2 ^ 32 := hp.valid.2.2.2.2.2.2.2.2.2.1
  have l3 : (arg s₀ 10).toNat < 2 ^ 32 := hp.valid.2.2.2.2.2.2.2.2.2.2.1
  have l4 : (arg s₀ 12).toNat < 2 ^ 32 := hp.valid.2.2.2.2.2.2.2.2.2.2.2
  unfold Impl.Argon2.RISCV64.Derive.code
  refine WP.seq ((start_ok hp h pr).mono fun s₁ h₁ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 1) (len := 2) (by decide) (by decide) (by simp) l1
    (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 3) (len := 4) (by decide) (by decide) (by simp) l2
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₂).mono fun s₃ h₃ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 9) (len := 10) (by decide) (by decide) (by simp) l3
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₃).mono fun s₄ h₄ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 11) (len := 12) (by decide) (by decide) (by simp) l4
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₄).mono fun s₅ h₅ => ?_)
  refine (finish_ok hp h₅).mono fun t ⟨it, pt, bt⟩ => ⟨it, pt, ?_⟩
  rw [bt, Proof.Argon2.initialHash_stream, List.take_of_length_le (by rw [finalHash_length])]
  rfl

end

end VG.Proof.Argon2.RISCV64.Derive
