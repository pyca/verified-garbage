module

public import VerifiedGarbage.Proof.Sha3.X86_64.Permute
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Tree
public import VerifiedGarbage.Spec.SlhDsa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# SLH-DSA (SHAKE) on x86-64: one instruction at a time, for `levels`

Weakest-precondition rules for the instruction forms of
`Impl/SlhDsa/X86_64/Tree.lean` that `Proof/Sha3/X86_64/Permute.lean` has no
rule for, in its style (`Upd`), and the facts about their values the proof
of `levels` needs: the bytes a `setFieldR` stores (`bswapStore_bytes`), the
mask of a comparison (`mask_eq`), and `mulN`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Proof.Sha3.X86_64 (Upd WP.cons)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov r32, r32`, which zero-extends. -/
theorem wp_mov32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `bswap r32`, which zero-extends. -/
theorem wp_bswap32 {d : Reg}
    (k : ∀ s', Upd s s' d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap32 d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `mov dword [m], r32`. -/
theorem wp_store32 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store32 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 32) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store32, ha, hout]

/-- `shr r64, cl`. -/
theorem wp_shrcl {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d >>> ((s.gpr .rcx).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.shiftCl .shr d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.withFlags _ _ _ _ _ _ _))

/-- `shl r64, n`, `1 ≤ n ≤ 63`. -/
theorem wp_shl {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d <<< n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shl d n :: is)) s Q := by
  have e : exec (.shift .shl d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (64 - n)))
      (if n = 1 then some ((s.gpr d <<< n).msb ^^ (s.gpr d).getLsbD (64 - n)) else none)
      (some (s.gpr d <<< n == 0)) (some (s.gpr d <<< n).msb)).setReg d (s.gpr d <<< n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.withFlags _ _ _ _ _ _ _))

/-- `shr r64, n`, `1 ≤ n ≤ 63`. -/
theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  have e : exec (.shift .shr d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
      (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
      (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.withFlags _ _ _ _ _ _ _))

/-- `add r64, r64`. -/
theorem wp_add {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `sub r64, r64`. -/
theorem wp_sub {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp r64, r64`, setting ZF and CF. -/
theorem wp_cmpr {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d - s.gpr r == 0) → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

/-- `cmp r64, imm32`, setting ZF. -/
theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

/-- `and r64, r64`. -/
theorem wp_and {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

/-! ## Values -/

/-- A sign-extended immediate below `2³¹`. -/
theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_using [h]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

/-- The mask of `x = 0` for `x < 2⁶³`: `-((x - 1) ≫ 63)`. -/
theorem mask_eq {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (0 : BitVec 64) - (x - 1) >>> 63 = if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · rw [ite_eq_right h]
    have h1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using e)) h
      · exact e
    have hl := x.isLt
    have e : (x - 1).toNat = x.toNat - 1 := by
      rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega_using [h1, hl]
    have : (x - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow, show (0 : BitVec 64).toNat = 0 from rfl]
      exact Nat.div_eq_of_lt (by omega_using [hx])
    rw [this]; rfl

/-- A masked word: all of it, or nothing. -/
theorem and_mask (v : BitVec 64) (c : Prop) [Decidable c] :
    v &&& (if c then BitVec.allOnes 64 else 0) = if c then v else 0 := by
  split
  · exact BitVec.and_allOnes
  · exact BitVec.and_zero

/-- `mulN`'s product. -/
theorem mulN_val {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) (x : BitVec 64) :
    (if n = 24 then x <<< 4 + x <<< 3 else x <<< (if n = 16 then 4 else 5)) = x * BitVec.ofNat 64 n := by
  rcases hn with rfl | rfl | rfl
  · simp only [Nat.reduceEqDiff, ite_false, ite_true]
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
  · simp only [ite_true]
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, ← BitVec.mul_add]; rfl
  · simp only [Nat.reduceEqDiff, ite_false]
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl


/-! ## Bytes of `scratch`

Every address `levels` touches but the authentication path's is `S + o`,
`S` the base of `scratch` and `o` below `2¹⁶` (`at' S o`, `S.toNat + 2¹⁶ ≤ 2⁶⁴`). -/

/-- `S + a + b = S + (a + b)`. -/
theorem add_add (S : Addr) (a b : Nat) : S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Byte `j` of a 32-bit value stored after `bswap`: byte `j` of `v` big-endian. -/
theorem bswap_byte (v : BitVec 64) {j : Nat} (hj : j < 4) :
    (bswap32 (v.setWidth 32)).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (v.toNat / 256 ^ (3 - j)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h256 : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by rw [Nat.pow_mul]
  rw [h256]
  unfold bswap32
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
    Nat.testBit_div_two_pow, BitVec.testBit_toNat, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
    decide_true, Bool.true_and, ↓reduceIte]

/-- The 32-bit field at `S + o` after `setFieldR`'s store of `v`: `toByte v 4`. -/
theorem field_bytes (m : Mem) (S : Addr) (o : Nat)
    (v : BitVec 64) {j : Nat} (hj : j < 4) :
    (m.writeW (S + BitVec.ofNat 64 o) (bswap32 (v.setWidth 32))) (S + BitVec.ofNat 64 (o + j)) =
      (Spec.SlhDsa.toByte v.toNat 4).getD j 0 := by
  rw [← add_add, writeW_byte _ _ _ (by omega_using [hj]) (by decide), bswap_byte _ hj]
  simp only [Spec.SlhDsa.toByte, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

/-- A byte of `scratch` after a write of 8 bytes at `o`: the written byte, or
the byte that was there. -/
theorem byte_write8 (m : Mem) (S : Addr) {o q : Nat} (ho : o + 8 ≤ 2 ^ 16) (hq : q < 2 ^ 16) (v : BitVec 64) :
    (m.writeW (S + BitVec.ofNat 64 o) v) (S + BitVec.ofNat 64 q) =
      if o ≤ q ∧ q < o + 8 then v.extractLsb' (8 * (q - o)) 8 else m (S + BitVec.ofNat 64 q) := by
  split
  · rename_i h
    rw [show S + BitVec.ofNat 64 q = S + BitVec.ofNat 64 o + BitVec.ofNat 64 (q - o) by
        rw [add_add, show o + (q - o) = q by omega_using [h]],
      writeW_byte _ _ _ (by omega_using [h]) (by decide)]
  · rename_i h
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' _ (by omega_using [ho]) (by omega_using [hq])]
    split <;> rename_i hs <;> omega_using [h, hs, ho, hq]

/-- A word of `scratch`, from its bytes. -/
theorem readW_bytes (m : Mem) (S : Addr) (o : Nat) (j : Nat) (hj : j < 8) :
    (m.readW (S + BitVec.ofNat 64 o) 64).extractLsb' (8 * j) 8 = m (S + BitVec.ofNat 64 (o + j)) := by
  rw [byte_readW _ _ (by omega_using [hj]), add_add]

/-- `scratch` as a writable region. -/
theorem in_scr {wr : List Region} {S : Addr} (h : ⟨S, 2 ^ 16⟩ ∈ wr) {o n : Nat} (ho : o + n ≤ 2 ^ 16) :
    InRegions wr (S + BitVec.ofNat 64 o) n :=
  ⟨_, h, Offset.contains_base _ ho (by omega_using [ho])⟩

/-- `scratch` as a readable region. -/
theorem in_scr' {rd wr : List Region} {S : Addr} (h : ⟨S, 2 ^ 16⟩ ∈ wr) {o n : Nat} (ho : o + n ≤ 2 ^ 16) :
    InRegions (rd ++ wr) (S + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := in_scr (wr := wr) h ho
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The `8w` bytes from `S + b + d₁` copied to `S + a + d₂`, a word at a time
through `rax` (`copyWords`), the two ranges separate. -/
theorem copy_ok {S : Addr} {t sr : Reg} (ht : t ≠ .rax) (hsr : sr ≠ .rax) {a b d₁ d₂ : Nat} :
    ∀ (w : Nat) (s : State), s.gpr t = S + BitVec.ofNat 64 a → s.gpr sr = S + BitVec.ofNat 64 b →
      (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr → b + d₁ + 8 * w ≤ 2 ^ 16 → a + d₂ + 8 * w ≤ 2 ^ 16 →
      (b + d₁ + 8 * w ≤ a + d₂ ∨ a + d₂ + 8 * w ≤ b + d₁) →
      WP isa (.block (Impl.SlhDsa.X86_64.copyWords t d₂ sr d₁ w)) s (fun s' =>
        (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ i < 8 * w, s'.mem (S + BitVec.ofNat 64 (a + d₂ + i)) = s.mem (S + BitVec.ofNat 64 (b + d₁ + i))) ∧
        Frame [⟨S + BitVec.ofNat 64 (a + d₂), 8 * w⟩] s.mem s'.mem) := by
  intro w
  induction w with
  | zero =>
    intro s _ _ _ _ _ _
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩
  | succ w ih =>
    intro s h₁ h₂ hw hb ha hsep
    have e : Impl.SlhDsa.X86_64.copyWords t d₂ sr d₁ (w + 1) = Impl.SlhDsa.X86_64.copyWords t d₂ sr d₁ w ++
        ([.mov .rax (.mem (Impl.Sha3.X86_64.at_ sr (d₁ + 8 * w))), .store (Impl.Sha3.X86_64.at_ t (d₂ + 8 * w)) .rax] :
          List Instr) := by
      simp [Impl.SlhDsa.X86_64.copyWords, List.range_succ, List.flatMap_append]
    rw [e]
    refine WP.block_append (WP.mono (ih s h₁ h₂ hw (by omega_using [hb]) (by omega_using [ha])
      (by omega_using [hsep])) fun s₁ ⟨g₁, r₁, w₁, c₁, f₁⟩ => ?_)
    refine Proof.Sha3.X86_64.wp_movm (a := S + BitVec.ofNat 64 (b + d₁ + 8 * w))
      (by rw [Proof.Sha3.X86_64.ea_at, g₁ _ hsr, h₂, add_add, Nat.add_assoc])
      (by rw [r₁, w₁]; exact in_scr' hw (by omega_using [hb])) fun s₂ u₂ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := S + BitVec.ofNat 64 (a + d₂ + 8 * w))
      (by rw [Proof.Sha3.X86_64.ea_at, u₂.other _ ht, g₁ _ ht, h₁, add_add, Nat.add_assoc])
      (by rw [u₂.wr, w₁]; exact in_scr hw (by omega_using [ha])) fun s₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
    -- the source bytes are as they were
    have hsrc : ∀ i < 8 * (w + 1), s₁.mem (S + BitVec.ofNat 64 (b + d₁ + i)) = s.mem (S + BitVec.ofNat 64 (b + d₁ + i)) := by
      intro i hi
      refine f₁ _ fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      intro hc
      simp only [Region.Contains] at hc
      rw [Offset.sub_toNat' _ (by omega_using [ha]) (by omega_using [hb, hi])] at hc
      split at hc <;> rename_i hs <;> omega_using [hc, hs, hsep, hi, ha, hb]
    refine ⟨fun g hg => by rw [g₃, u₂.other _ hg, g₁ _ hg], by rw [r₃, u₂.rd, r₁], by rw [w₃, u₂.wr, w₁],
      fun i hi => ?_, ?_⟩
    · rw [m₃, u₂.mem, u₂.gpr, byte_write8 _ _ (by omega_using [ha]) (by omega_using [ha, hi])]
      split
      · rename_i h
        rw [readW_bytes _ _ _ _ (by omega_using [h]), show b + d₁ + 8 * w + (a + d₂ + i - (a + d₂ + 8 * w)) =
          b + d₁ + i by omega_using [h], hsrc i hi]
      · rename_i h
        rw [c₁ i (by omega_using [h, hi])]
    · rw [m₃, u₂.mem]
      have hsub : Frame [⟨S + BitVec.ofNat 64 (a + d₂), 8 * (w + 1)⟩] s.mem s₁.mem := Frame.sub f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
      refine hsub.writeW (List.mem_singleton_self _) _ ?_
      rw [show S + BitVec.ofNat 64 (a + d₂ + 8 * w) = S + BitVec.ofNat 64 (a + d₂) + BitVec.ofNat 64 (8 * w) by
        rw [add_add]]
      exact Offset.contains_base _ (by omega_using []) (by omega_using [ha])

/-- A byte after a write of 8 bytes at `p + o`, for any base `p`. -/
theorem byte_write8' (m : Mem) (p : Addr) {o q : Nat} (ho : o + 8 ≤ 2 ^ 64) (hq : q < 2 ^ 64) (v : BitVec 64) :
    (m.writeW (p + BitVec.ofNat 64 o) v) (p + BitVec.ofNat 64 q) =
      if o ≤ q ∧ q < o + 8 then v.extractLsb' (8 * (q - o)) 8 else m (p + BitVec.ofNat 64 q) := by
  split
  · rename_i h
    rw [show p + BitVec.ofNat 64 q = p + BitVec.ofNat 64 o + BitVec.ofNat 64 (q - o) by
        rw [add_add, show o + (q - o) = q by omega_using [h]],
      writeW_byte _ _ _ (by omega_using [h]) (by decide)]
  · rename_i h
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' _ (by omega_using [ho]) hq]
    split <;> rename_i hs <;> omega_using [h, hs, ho, hq]

/-- `mulN n r tmp`: `r ← r·n`, through `tmp`. -/
theorem mulN_ok {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) {r tmp : Reg} (hrt : r ≠ tmp) {is : List Instr} {s : State}
    {Q : State → Prop}
    (k : ∀ s', s'.gpr r = s.gpr r * BitVec.ofNat 64 n → (∀ g, g ≠ r → g ≠ tmp → s'.gpr g = s.gpr g) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Wots.mulN n r tmp ++ is)) s Q := by
  rcases hn with rfl | rfl | rfl
  · refine wp_shl (by decide) (by decide) fun s₁ u₁ => k s₁ ?_ (fun g h _ => u₁.other _ h) u₁.mem u₁.rd u₁.wr
    rw [u₁.gpr, BitVec.shiftLeft_eq_mul_twoPow]; rfl
  · refine Proof.Sha3.X86_64.wp_mov fun s₁ u₁ => wp_shl (by decide) (by decide) fun s₂ u₂ =>
      wp_shl (by decide) (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => k s₄ ?_ (fun g h h' => ?_) ?_ ?_ ?_
    · rw [u₄.gpr, u₃.other _ hrt, u₂.gpr, u₁.other _ hrt, u₃.gpr, u₂.other _ hrt.symm, u₁.gpr,
        BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow, ← BitVec.mul_add]; rfl
    · rw [u₄.other _ h, u₃.other _ h', u₂.other _ h, u₁.other _ h']
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · refine wp_shl (by decide) (by decide) fun s₁ u₁ => k s₁ ?_ (fun g h _ => u₁.other _ h) u₁.mem u₁.rd u₁.wr
    rw [u₁.gpr, BitVec.shiftLeft_eq_mul_twoPow]; rfl

/-- The masked XOR of `W` words (`scanBody`'s last part): the `8W` bytes at
`au` (`r13`) XORed with those at `nd` (`rdx`) if the mask in `rdi` is all
ones (`c`), and kept if it is zero. -/
theorem xorWords_ok {c : Prop} [Decidable c] {nd au : Addr} :
    ∀ (W : Nat) (s : State), s.gpr .rdx = nd → s.gpr .r13 = au →
      s.gpr .rdi = (if c then BitVec.allOnes 64 else 0) →
      (∀ w < W, InRegions (s.rd ++ s.wr) (nd + BitVec.ofNat 64 (8 * w)) 8) →
      (∀ w < W, InRegions s.wr (au + BitVec.ofNat 64 (8 * w)) 8) →
      Region.Disjoint ⟨nd, 8 * W⟩ ⟨au, 8 * W⟩ → 8 * W ≤ 2 ^ 64 →
      WP isa (.block ((List.range W).flatMap fun w =>
          [.mov .rax (.mem (Impl.Sha3.X86_64.at_ .rdx (8 * w))), .alu .and .rax (.reg .rdi),
            .alu .xor .rax (.mem (Impl.Sha3.X86_64.at_ .r13 (8 * w))), .store (Impl.Sha3.X86_64.at_ .r13 (8 * w)) .rax]))
        s (fun s' => (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
          (∀ j < 8 * W, s'.mem (au + BitVec.ofNat 64 j) =
            (if c then s.mem (nd + BitVec.ofNat 64 j) else 0) ^^^ s.mem (au + BitVec.ofNat 64 j)) ∧
          Frame [⟨au, 8 * W⟩] s.mem s'.mem) := by
  intro W
  induction W with
  | zero =>
    intro s _ _ _ _ _ _ _
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun j hj => absurd hj (by omega_using []), Frame.refl _ _⟩
  | succ W ih =>
    intro s h₁ h₂ h₃ hin hout hd hW
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih s h₁ h₂ h₃ (fun w hw => hin w (by omega_using [hw]))
      (fun w hw => hout w (by omega_using [hw])) (hd.sub_left (Region.sub_prefix (by omega_using []))
        |>.sub_right (Region.sub_prefix (by omega_using []))) (by omega_using [hW]))
      fun s₁ ⟨g₁, r₁, w₁, c₁, f₁⟩ => ?_)
    refine Proof.Sha3.X86_64.wp_movm (a := nd + BitVec.ofNat 64 (8 * W))
      (by rw [Proof.Sha3.X86_64.ea_at, g₁ _ (by decide), h₁]) (by rw [r₁, w₁]; exact hin W (by omega_using [])) fun s₂ u₂ => ?_
    refine Proof.Sha3.X86_64.wp_and fun s₃ u₃ => ?_
    refine Proof.Sha3.X86_64.wp_xorm (a := au + BitVec.ofNat 64 (8 * W))
      (by rw [Proof.Sha3.X86_64.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h₂])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, r₁, w₁]
          obtain ⟨r, hr, hc⟩ := hout W (by omega_using [])
          exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₄ u₄ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := au + BitVec.ofNat 64 (8 * W))
      (by rw [Proof.Sha3.X86_64.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide), h₂])
      (by rw [u₄.wr, u₃.wr, u₂.wr, w₁]; exact hout W (by omega_using [])) fun s₅ g₅ m₅ r₅ w₅ => WP.block_nil ?_
    have hm : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have hrdi : s₂.gpr .rdi = (if c then BitVec.allOnes 64 else 0) := by rw [u₂.other _ (by decide), g₁ _ (by decide), h₃]
    -- the node's bytes, and the authentication path's past the words written, are as they were
    have hnd : ∀ j < 8 * (W + 1), s₁.mem (nd + BitVec.ofNat 64 j) = s.mem (nd + BitVec.ofNat 64 j) := fun j hj =>
      Frame.bytes (R := ⟨nd, 8 * (W + 1)⟩) f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd.sub_right (Region.sub_prefix (by omega_using []))) (by omega_using [hW]) hj
    have hau : ∀ j, 8 * W ≤ j → j < 8 * (W + 1) → s₁.mem (au + BitVec.ofNat 64 j) = s.mem (au + BitVec.ofNat 64 j) := by
      intro j h1 h2
      refine f₁ _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
      rw [Nat.mod_eq_of_lt (by omega_using [hW, h2])] at hc
      omega_using [hc, h1]
    refine ⟨fun g hg => by rw [g₅, u₄.other _ hg, u₃.other _ hg, u₂.other _ hg, g₁ _ hg], by rw [r₅, u₄.rd, u₃.rd, u₂.rd, r₁],
      by rw [w₅, u₄.wr, u₃.wr, u₂.wr, w₁], fun j hj => ?_, ?_⟩
    · rw [m₅, hm, byte_write8' _ _ (by omega_using [hW]) (by omega_using [hW, hj])]
      split
      · rename_i h
        have e1 : 8 * W + (j - 8 * W) = j := by omega_using [h]
        have hm3 : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
        rw [u₄.gpr, u₃.gpr, u₂.gpr, hrdi, and_mask, BitVec.extractLsb'_xor, hm3,
          readW_bytes _ _ _ _ (by omega_using [h]), e1, hau j h.1 h.2]
        by_cases hc : c
        · rw [ite_eq_left hc, ite_eq_left hc, readW_bytes _ _ _ _ (by omega_using [h]), e1, hnd j hj]
        · rw [ite_eq_right hc, ite_eq_right hc]; simp
      · rename_i h
        rw [c₁ j (by omega_using [h, hj])]
    · rw [m₅, hm]
      have hsub : Frame [⟨au, 8 * (W + 1)⟩] s.mem s₁.mem := Frame.sub f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
      exact hsub.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hW]))

end VG.Proof.SlhDsa.X86_64.Levels
