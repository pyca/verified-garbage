module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# Numbers to and from big-endian bytes, and constants, on RISC-V

`loadNum` reads a big-endian number of `8 k` bytes into a slot, a doubleword
at a time from the most significant (`loadNum_ok`, from `be64_toNat`: a
big-endian doubleword is its bytes); `storeNum` writes a slot's number under
a mask big-endian (`storeNum_ok`: the bytes are `toBytes` of the number, or
zeros); `setConst` stores a constant from immediates (`setConst_ok`).
`loadLen` and `storeLen` do the same for a number of any length, its top
word of fewer than eight bytes a byte at a time (`loadLen_ok`,
`storeLen_ok`), and are `loadNum` and `storeNum` for whole words
(`loadLen_mul`, `storeLen_mul`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Mont
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.RISCV64.ByteLoad (be64 beBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.Spec.Weierstrass (ofBytes toBytes)

theorem add_ofNat_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- A big-endian doubleword is its eight bytes. -/
theorem be64_toNat (m : Mem) (p : Addr) (off : Nat) :
    (be64 m p off).toNat = ofBytes (bytesAt m (p + BitVec.ofNat 64 off) 8) := by
  rw [show bytesAt m (p + BitVec.ofNat 64 off) 8 = [m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 0),
      m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 4),
      m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 5), m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 6),
      m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 7)] from rfl]
  simp only [add_ofNat_add, Nat.add_zero, be64, BitVec.toNat_append, shl8_or, ofBytes, List.foldl_cons,
    List.foldl_nil]
  omega

/-- A number's top word. -/
theorem wordsVal_top (m : Mem) (b : Addr) : ∀ (a k : Nat),
    wordsVal m b a (k + 1) = wordsVal m b a k + 2 ^ (64 * k) * (word m b (a + 8 * k)).toNat
  | a, 0 => by simp [wordsVal]
  | a, k + 1 => by
    rw [wordsVal, wordsVal_top m b (a + 8) k, wordsVal, pow64_succ,
      show a + 8 + 8 * k = a + 8 * (k + 1) by omega]
    rw [Nat.mul_add, Nat.mul_assoc]
    omega

/-- The bytes of a number of `a + b` bytes: its top `a`, then its low `b`. -/
theorem toBytes_add (a b x : Nat) : toBytes (a + b) x = toBytes a (x >>> (8 * b)) ++ toBytes b x := by
  rw [Nat.add_comm a b]
  simp only [toBytes, List.range_add, List.reverse_append, List.map_append, List.map_reverse, List.map_map]
  congr 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.mul_add, Nat.shiftRight_add]

/-- The low `b` bytes depend only on the number modulo `2^(8 b)`. -/
theorem toBytes_mod (b x w : Nat) : toBytes b (x + 2 ^ (8 * b) * w) = toBytes b x := by
  simp only [toBytes]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e : 2 ^ (8 * b) = 2 ^ (8 * i) * (256 * 2 ^ (8 * (b - i - 1))) := by
    rw [show 256 = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `storeBE`'s bytes are `toBytes`. -/
theorem beBytes_eq (v : BitVec 64) : beBytes 8 v = toBytes 8 v.toNat := by
  simp only [beBytes, toBytes]
  rw [show (List.range 8).reverse = (List.range 8).map (fun j => 8 - 1 - j) from rfl, List.map_map]
  apply List.map_congr_left
  intro j _
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]

/-- Bytes apart from the working space survive a change within it. -/
theorem bytesAt_out {base q : Addr} {o len n : Nat} {m m' : Mem} (h : Outside base o len m m') (hl : o + len ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := hsep i hi
  simp only [Region.Contains] at this
  exact h _ (.inr (by simp only [ofs]; omega))

/-- `loadNum`: the `8 k` bytes at `p + off`, big-endian, to the slot at `o`. -/
theorem loadNum_ok : ∀ (k : Nat) {s : State} {base : Addr} {o : Nat} {p : Reg} {off : Nat},
    WsReg s base → p ∉ [Reg.t0, .t1] → o % 8 = 0 → o + 8 * k ≤ 4096 → off + 8 * k ≤ 2048 →
    (∀ j < k, InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 (off + 8 * j)) 8) →
    (∀ i < 8 * k, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + i)) 1) →
    WP isa (.block (loadNum k o p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * k) s.mem s'.mem ∧
      wordsVal s'.mem base o k = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) (8 * k))
  | 0, s, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Outside.refl _ _ _ _, rfl⟩
  | k + 1, s, base, o, p, off, hw, hp, ho, ho', hoff, hin, hsep => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
    rw [loadNum, List.append_assoc]
    refine WP.block_append (WP.mono (VG.RISCV64.ByteLoad.loadBE64_ok (d := .t0) (tmp := .t1) (n := p) (off := off)
      (Ne.symm hp.1) (Ne.symm hp.2) (by decide) (by omega) (by simpa using hin 0 (by omega))) fun s₁ e₁ => ?_)
    subst e₁
    have r₁ : Rest [.t0, .t1] s ((s.write .t1 ((s.mem (s.gpr p + BitVec.ofNat 64 (off + 7))).setWidth 64)).write .t0
        (be64 s.mem (s.gpr p) off)) :=
      ((Upd.write _ _ _).rest (by decide)).trans ((Upd.write _ _ _).rest (by decide))
    have hw₁ := hw.of_rest r₁
    refine sdAt_ws hw₁ (by decide) (d := o + 8 * k) (by omega) (by omega) fun s₂ u₂ => ?_
    have r₂ : Rest [.t0, .t1] s s₂ := r₁.trans (u₂.rest _)
    have O₂ : Outside base (o + 8 * k) 8 s.mem s₂.mem := by
      rw [u₂.mem]; exact writeW_outside _ _ _ (by omega)
    have g₂ : s₂.gpr p = s.gpr p := r₂.gpr _ (by simp [hp.1, hp.2])
    refine WP.mono (loadNum_ok k (hw.of_rest r₂) (p := p) (off := off + 8) (by simp [hp.1, hp.2]) ho (by omega)
      (by omega) (fun j hj => by
        rw [r₂.rd, r₂.wr, g₂, show off + 8 + 8 * j = off + 8 * (j + 1) by omega]
        exact hin (j + 1) (by omega))
      (fun i hi => by
        rw [g₂, show off + 8 + i = off + (8 + i) by omega]
        exact hsep _ (by omega)))
      fun s₃ ⟨r₃, O₃, e₃⟩ => ⟨r₂.trans r₃, (O₂.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega)), ?_⟩
    have e₃' : wordsVal s₃.mem base o k = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 (off + 8)) (8 * k)) := by
      rw [e₃, g₂, bytesAt_out O₂ (by omega) (fun i hi => by
        rw [add_ofNat_add, show off + 8 + i = off + (8 + i) by omega]; exact hsep (8 + i) (by omega))]
    rw [wordsVal_top, e₃', O₃.word (by omega) (by omega), u₂.mem, word_writeW_self]
    simp only [State.write, ↓reduceIte]
    rw [be64_toNat, show 8 * (k + 1) = 8 + 8 * k by omega, bytesAt_add, ofBytes_append, length_bytesAt,
      add_ofNat_add, show (256 : Nat) ^ (8 * k) = 2 ^ (64 * k) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
    rw [Nat.mul_comm (2 ^ (64 * k))]
    omega

/-- `setConst`: `x mod 2^(64 k)` to the slot at `o`. -/
theorem setConst_ok : ∀ (k : Nat) {s : State} {base : Addr} {o x : Nat},
    WsReg s base → o % 8 = 0 → o + 8 * k ≤ 4096 →
    WP isa (.block (setConst k o x)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * k) s.mem s'.mem ∧ wordsVal s'.mem base o k = x % 2 ^ (64 * k)
  | 0, s, _, _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Outside.refl _ _ _ _, by simp [wordsVal, Nat.mod_one]⟩
  | k + 1, s, base, o, x, hw, ho, ho' => by
    rw [setConst, List.append_assoc]
    refine WP.block_append (WP.mono (VG.RISCV64.ByteLoad.li64_ok (s := s) (d := .t0) (tmp := .t1) (by decide)
      (BitVec.ofNat 64 x)) fun s₁ e₁ => ?_)
    subst e₁
    have r₁ : Rest [.t0, .t1] s ((s.write .t1 (sext32 ((BitVec.ofNat 64 x).setWidth 32))).write .t0
        (BitVec.ofNat 64 x)) :=
      ((Upd.write _ _ _).rest (by decide)).trans ((Upd.write _ _ _).rest (by decide))
    refine sdAt_ws (hw.of_rest r₁) (by decide) (d := o) (by omega) ho fun s₂ u₂ => ?_
    have r₂ : Rest [.t0, .t1] s s₂ := r₁.trans (u₂.rest _)
    have O₂ : Outside base o 8 s.mem s₂.mem := by rw [u₂.mem]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (setConst_ok k (hw.of_rest r₂) (o := o + 8) (x := x >>> 64) (by omega) (by omega))
      fun s₃ ⟨r₃, O₃, e₃⟩ => ⟨r₂.trans r₃, (O₂.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega)), ?_⟩
    rw [wordsVal, e₃, O₃.word (by omega) (by omega), u₂.mem, word_writeW_self, pow64_succ, Nat.mod_mul,
      Nat.shiftRight_eq_div_pow]
    simp only [State.write, ↓reduceIte, BitVec.toNat_ofNat]

open VG.WriteBytes in
/-- Bytes written apart from the working space keep it. -/
theorem writeBytes_unch {base Q : Addr} {xs : List Byte} (m : Mem)
    (hsep : ∀ i < xs.length, ¬ (⟨base, 8192⟩ : Region).Contains (Q + BitVec.ofNat 64 i) 1) :
    VG.Proof.Weierstrass.Unch base [(8192, 2 ^ 64)] m (writeBytes m Q xs) := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  have hlt := (x - base).isLt
  simp only [ofs] at h
  have h' : (x - base).toNat < 8192 := by omega
  simp only [writeBytes]
  split
  · rename_i hi
    exfalso
    refine hsep _ hi ?_
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    show (x - base).toNat + 1 ≤ 8192
    omega
  · rfl

open VG.WriteBytes in
/-- `storeNum`: the slot's number under the mask, or zeros, big-endian at
`q + off`. -/
theorem storeNum_ok (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {a : Nat} {q : Reg} {off : Nat},
    WsReg s base → s.gpr .a7 = maskOf c → q ∉ [Reg.t0, .t1] → a % 8 = 0 → a + 8 * k ≤ 4096 →
    off + 8 * k ≤ 2048 →
    (∀ i < 8 * k, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + i)) 1) →
    (∀ i < 8 * k, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + i)) 1) →
    WP isa (.block (storeNum k a q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes (8 * k) (if c then wordsVal s.mem base a k else 0))
  | 0, s, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, by
      simp only [Nat.mul_zero]; rfl⟩
  | k + 1, s, base, a, q, off, hw, hc, hq, ha, ha', hoff, hout, hsep => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [storeNum, List.cons_append, List.append_assoc]
    refine ldAt_ws hw (d := a + 8 * k) (by omega) (by omega) fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
    have r₂ : Rest [.t0, .t1] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
    have g₂ : s₂.gpr q = s.gpr q := r₂.gpr _ (by simp [hq.1, hq.2])
    have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
    have v₂ : s₂.gpr .t0 = word s.mem base (a + 8 * k) &&& maskOf c := by
      rw [u₂.gpr, u₁.gpr, u₁.other .a7 (by decide), hc]
    rw [List.nil_append]
    refine WP.block_append (WP.mono (VG.RISCV64.ByteLoad.storeBE_ok (s := s₂) (v := .t0) (tmp := .t1) (n := q)
      (off := off) (w := 8) (by decide) (Ne.symm hq.2) (by decide) (by decide) (by omega) (fun j hj => by
        rw [r₂.wr, g₂]; exact hout j (by omega))) fun s₃ e₃ => ?_)
    have hB : (beBytes 8 (s₂.gpr .t0)).length = 8 := VG.RISCV64.ByteLoad.beBytes_length _ _
    have U₃ := writeBytes_unch (base := base) (Q := s.gpr q + BitVec.ofNat 64 off) (xs := beBytes 8 (s₂.gpr .t0))
      s.mem (fun i hi => by rw [hB] at hi; rw [add_ofNat_add]; exact hsep i (by omega))
    have mem₃ : s₃.mem = writeBytes s₂.mem (s₂.gpr q + BitVec.ofNat 64 off) (beBytes 8 (s₂.gpr .t0)) := by
      rw [e₃]; rfl
    have r₃ : Rest [.t0, .t1] s₂ s₃ := ⟨fun r hr => by
      have : r ≠ .t1 := fun h => hr (by simp [h])
      rw [e₃]; simp only [State.write, this, ↓reduceIte], by rw [e₃]; rfl, by rw [e₃]; rfl, by rw [e₃]; rfl⟩
    have g₃ : s₃.gpr q = s.gpr q := (r₂.trans r₃).gpr _ (by simp [hq.1, hq.2])
    refine WP.mono (storeNum_ok c k ((hw.of_rest r₂).of_rest r₃) (a := a) (q := q) (off := off + 8)
      (by rw [(r₂.trans r₃).gpr _ (by decide), hc]) (by simp [hq.1, hq.2]) ha
      (by omega) (by omega)
      (fun i hi => by
        rw [(r₂.trans r₃).wr, g₃, show off + 8 + i = off + (8 + i) by omega]
        exact hout _ (by omega))
      (fun i hi => by
        rw [g₃, show off + 8 + i = off + (8 + i) by omega]
        exact hsep _ (by omega)))
      fun s₄ ⟨r₄, m₄⟩ => ⟨(r₂.trans r₃).trans r₄, ?_⟩
    have hwa := writeBytes_append s.mem (s.gpr q + BitVec.ofNat 64 off) (beBytes 8 (s₂.gpr .t0))
      (toBytes (8 * k) (if c then wordsVal s.mem base a k else 0)) (by
        rw [hB, VG.Proof.Weierstrass.length_toBytes]; omega)
    rw [hB, add_ofNat_add] at hwa
    rw [m₄, mem₃, g₃, g₂, m₂]
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hwa]
    congr 1
    rw [v₂, beBytes_eq, wordsVal_top, show 8 * (k + 1) = 8 + 8 * k by omega, toBytes_add]
    have hX := wordsVal_lt s.mem base a k
    cases c
    · simp [maskOf]
    · simp only [maskOf, ↓reduceIte, BitVec.and_allOnes]
      have e1 : (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) >>> (8 * (8 * k)) =
          (word s.mem base (a + 8 * k)).toNat := by
        rw [Nat.shiftRight_eq_div_pow, show 8 * (8 * k) = 64 * k by omega, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt hX, Nat.zero_add]
      rw [e1, show 2 ^ (64 * k) = 2 ^ (8 * (8 * k)) by congr 1; omega, toBytes_mod]

/-! ## Numbers of any length in bytes -/

/-- One byte of `loadBytesBE`: `t0` shifted up a byte, the byte at
`p + off` or'ed in. -/
theorem loadByte_ok {s : State} {p : Reg} {off : Nat} (h0 : p ≠ .t0) (ho : off < 2048)
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 1) :
    WP isa (.block [.shift .sll .d .t0 .t0 8, .load .b .t1 p off, .logic .or .t0 .t0 .t1]) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .t0 = s.gpr .t0 <<< 8 ||| (s.mem (s.gpr p + BitVec.ofNat 64 off)).setWidth 64 := by
  refine wp_sll (by decide) fun s₁ u₁ => ?_
  refine wp_lbu (off := off) ho (by rw [u₁.other _ h0]) (by rw [u₁.rd, u₁.wr]; exact h) fun s₂ u₂ => ?_
  refine wp_or fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem]

/-- `loadBytesBE`: `t0` shifted up by the `k` bytes at `p + off`, read in. -/
theorem loadBytesBE_ok : ∀ (k : Nat) {s : State} {p : Reg} {off : Nat},
    p ∉ [Reg.t0, .t1] → off + k ≤ 2048 → k ≤ 8 → (s.gpr .t0).toNat < 256 ^ (8 - k) →
    (∀ i < k, InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 (off + i)) 1) →
    WP isa (.block (loadBytesBE k p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = s.mem ∧
      (s'.gpr .t0).toNat = (s.gpr .t0).toNat * 256 ^ k + ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) k)
  | 0, s, _, _, _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, rfl, by simp [bytesAt, ofBytes]⟩
  | k + 1, s, p, off, hp, ho, hk, hv, hin => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
    rw [loadBytesBE]
    have h0 := hin 0 (by omega)
    rw [Nat.add_zero] at h0
    refine WP.block_append (WP.mono (loadByte_ok hp.1 (by omega) h0)
      fun s₁ ⟨r₁, m₁, e₁⟩ => ?_)
    generalize hB : s.mem (s.gpr p + BitVec.ofNat 64 off) = B at e₁
    have hb := B.isLt
    have g₁ := r₁.gpr p (by simp [hp.1, hp.2])
    have eX : (256 : Nat) ^ (8 - k) = 256 ^ (8 - (k + 1)) * 256 := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hX : (256 : Nat) ^ (8 - k) ≤ 2 ^ 64 :=
      Nat.le_trans (Nat.pow_le_pow_right (n := 256) (by decide) (show 8 - k ≤ 8 by omega)) (by decide)
    have v₁ : (s₁.gpr .t0).toNat = (s.gpr .t0).toNat * 256 + B.toNat := by
      rw [e₁, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (show (s.gpr .t0).toNat * 2 ^ 8 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show B.toNat < 2 ^ 64 by omega),
        ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (show B.toNat < 2 ^ 8 from hb), Nat.shiftLeft_eq]
    refine WP.mono (loadBytesBE_ok k (s := s₁) (p := p) (off := off + 1)
      (by simp [hp.1, hp.2]) (by omega) (by omega) (by rw [v₁]; omega) (fun i hi => ?_))
      fun s₂ ⟨r₂, m₂, e₂⟩ => ⟨r₁.trans r₂, by rw [m₂, m₁], ?_⟩
    · rw [g₁, r₁.rd, r₁.wr, show off + 1 + i = off + (i + 1) by omega]
      exact hin _ (by omega)
    · rw [e₂, g₁, v₁, m₁, show k + 1 = 1 + k by omega, bytesAt_add, ofBytes_append, length_bytesAt,
        add_ofNat_add]
      have e1 : bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) 1 = [B] := by
        simp [bytesAt, ← hB]
      rw [e1, show ofBytes [B] = B.toNat by simp [ofBytes], Nat.pow_add, Nat.pow_one, Nat.add_mul,
        Nat.mul_assoc, Nat.add_assoc]

/-- `loadLen`: the `len` bytes at `p + off`, big-endian, to the slot at `o`,
in `⌈len / 8⌉` words. -/
theorem loadLen_ok (len : Nat) {s : State} {base : Addr} {o : Nat} {p : Reg} {off L : Nat}
    (hw : WsReg s base) (hp : p ∉ [Reg.t0, .t1]) (ho : o % 8 = 0) (ho' : o + 8 * ((len + 7) / 8) ≤ 4096)
    (hoff : off + len ≤ L) (hL : L ≤ 2048) (hrd : (⟨s.gpr p, L⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < len, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (loadLen len o p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * ((len + 7) / 8)) s.mem s'.mem ∧
      wordsVal s'.mem base o ((len + 7) / 8) = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) len) := by
  have hin : ∀ {s₀ : State}, s₀.rd ++ s₀.wr = s.rd ++ s.wr → s₀.gpr p = s.gpr p → ∀ i n, i + n ≤ len →
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr p + BitVec.ofNat 64 (off + i)) n := fun e g i n hi => by
    rw [e, g]; exact ⟨_, hrd, Offset.contains_base _ (by omega) (by omega)⟩
  rw [loadLen]
  split
  · rename_i h8
    rw [List.nil_append, h8, Nat.add_zero, show (len + 7) / 8 = len / 8 by omega]
    refine WP.mono (loadNum_ok (len / 8) hw hp ho (by omega) (by omega) (fun j hj => hin rfl rfl _ _ (by omega))
      (fun i hi => hsep i (by omega))) fun s' ⟨r', O', e'⟩ => ⟨r', O', ?_⟩
    rw [e', show 8 * (len / 8) = len by omega]
  · rename_i h8
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
    have hq : (len + 7) / 8 = len / 8 + 1 := by omega
    rw [hq, List.append_assoc, List.append_assoc, List.singleton_append]
    refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
    have r₁ : Rest [.t0, .t1] s s₁ := u₁.rest (by decide)
    have g₁ : s₁.gpr p = s.gpr p := r₁.gpr _ (by simp [hp.1, hp.2])
    refine WP.block_append (WP.mono (loadBytesBE_ok (len % 8) (s := s₁) (p := p) (off := off)
      (by simp [hp.1, hp.2]) (by omega) (by omega) (by rw [u₁.gpr]; exact Nat.pow_pos (by decide))
      (fun i hi => hin (by rw [r₁.rd, r₁.wr]) g₁ _ _ (by omega))) fun s₂ ⟨r₂, m₂, e₂⟩ => ?_)
    have r₁₂ := r₁.trans r₂
    refine sdAt_ws (hw.of_rest r₁₂) (by decide) (d := o + 8 * (len / 8)) (by omega) (by omega) fun s₃ u₃ => ?_
    have r₃ : Rest [.t0, .t1] s s₃ := r₁₂.trans (u₃.rest _)
    have O₃ : Outside base (o + 8 * (len / 8)) 8 s.mem s₃.mem := by
      rw [u₃.mem, m₂, u₁.mem]; exact writeW_outside _ _ _ (by omega)
    have g₃ : s₃.gpr p = s.gpr p := r₃.gpr _ (by simp [hp.1, hp.2])
    refine WP.mono (loadNum_ok (len / 8) (hw.of_rest r₃) (p := p) (o := o) (off := off + len % 8)
      (by simp [hp.1, hp.2]) ho (by omega) (by omega)
      (fun j hj => by
        rw [show off + len % 8 + 8 * j = off + (len % 8 + 8 * j) by omega]
        exact hin (by rw [r₃.rd, r₃.wr]) g₃ _ _ (by omega))
      (fun i hi => by
        rw [g₃, show off + len % 8 + i = off + (len % 8 + i) by omega]
        exact hsep _ (by omega)))
      fun s₄ ⟨r₄, O₄, e₄⟩ => ⟨r₃.trans r₄, (O₃.mono (by omega) (by omega)).trans (O₄.mono (by omega) (by omega)), ?_⟩
    have e₄' : wordsVal s₄.mem base o (len / 8) =
        ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 (off + len % 8)) (8 * (len / 8))) := by
      rw [e₄, g₃, bytesAt_out O₃ (by omega) (fun i hi => by
        rw [add_ofNat_add, show off + len % 8 + i = off + (len % 8 + i) by omega]; exact hsep _ (by omega))]
    rw [wordsVal_top, e₄', O₄.word (by omega) (by omega), u₃.mem, word_writeW_self, e₂, u₁.gpr, g₁]
    rw [show len = len % 8 + 8 * (len / 8) by omega, bytesAt_add, ofBytes_append, length_bytesAt,
      add_ofNat_add, show (256 : Nat) ^ (8 * (len / 8)) = 2 ^ (64 * (len / 8)) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
    rw [show (len % 8 + 8 * (len / 8)) % 8 = len % 8 by omega, show (len % 8 + 8 * (len / 8)) / 8 = len / 8 by omega]
    rw [Nat.mul_comm (2 ^ (64 * (len / 8))), u₁.mem]
    omega

/-- `storeBE`'s `w` bytes are `toBytes`. -/
theorem beBytes_toBytes (w : Nat) (v : BitVec 64) : beBytes w v = toBytes w v.toNat := by
  apply List.ext_getElem (by simp [beBytes, toBytes]) fun i h₁ h₂ => ?_
  simp only [beBytes, toBytes, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]

open VG.WriteBytes in
/-- `storeLen`: the slot's number of `⌈len / 8⌉` words under the mask, or
zeros, in `len` bytes big-endian at `q + off`. -/
theorem storeLen_ok (c : Bool) (len : Nat) {s : State} {base : Addr} {a : Nat} {q : Reg} {off : Nat}
    (hw : WsReg s base) (hc : s.gpr .a7 = maskOf c) (hq : q ∉ [Reg.t0, .t1]) (ha : a % 8 = 0)
    (ha' : a + 8 * ((len + 7) / 8) ≤ 4096) (hoff : off + len ≤ 2048)
    (hout : ∀ i < len, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + i)) 1)
    (hsep : ∀ i < len, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (storeLen len a q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes len (if c then wordsVal s.mem base a ((len + 7) / 8) else 0)) := by
  rw [storeLen]
  split
  · rename_i h8
    rw [List.nil_append, h8, Nat.add_zero, show (len + 7) / 8 = len / 8 by omega]
    refine WP.mono (storeNum_ok c (len / 8) hw hc hq ha (by omega) (by omega) (fun i hi => hout i (by omega))
      (fun i hi => hsep i (by omega))) fun s' ⟨r', m'⟩ => ⟨r', ?_⟩
    rw [m', show 8 * (len / 8) = len by omega]
  · rename_i h8
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [show (len + 7) / 8 = len / 8 + 1 by omega]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ldAt_ws hw (d := a + 8 * (len / 8)) (by omega) (by omega) fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
    have r₂ : Rest [.t0, .t1] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
    have g₂ : s₂.gpr q = s.gpr q := r₂.gpr _ (by simp [hq.1, hq.2])
    have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
    have v₂ : s₂.gpr .t0 = word s.mem base (a + 8 * (len / 8)) &&& maskOf c := by
      rw [u₂.gpr, u₁.gpr, u₁.other .a7 (by decide), hc]
    refine WP.block_append (WP.mono (VG.RISCV64.ByteLoad.storeBE_ok (s := s₂) (v := .t0) (tmp := .t1) (n := q)
      (off := off) (w := len % 8) (by decide) (Ne.symm hq.2) (by omega) (by omega) (by omega) (fun j hj => by
        rw [r₂.wr, g₂]; exact hout j (by omega))) fun s₃ e₃ => ?_)
    have hB : (beBytes (len % 8) (s₂.gpr .t0)).length = len % 8 := VG.RISCV64.ByteLoad.beBytes_length _ _
    have U₃ := writeBytes_unch (base := base) (Q := s.gpr q + BitVec.ofNat 64 off)
      (xs := beBytes (len % 8) (s₂.gpr .t0)) s.mem (fun i hi => by
        rw [hB] at hi; rw [add_ofNat_add]; exact hsep i (by omega))
    have mem₃ : s₃.mem = writeBytes s₂.mem (s₂.gpr q + BitVec.ofNat 64 off) (beBytes (len % 8) (s₂.gpr .t0)) := by
      rw [e₃]; rfl
    have r₃ : Rest [.t0, .t1] s₂ s₃ := ⟨fun r hr => by
      have : r ≠ .t1 := fun h => hr (by simp [h])
      rw [e₃]; simp only [State.write, this, ↓reduceIte], by rw [e₃]; rfl, by rw [e₃]; rfl, by rw [e₃]; rfl⟩
    have g₃ : s₃.gpr q = s.gpr q := (r₂.trans r₃).gpr _ (by simp [hq.1, hq.2])
    refine WP.mono (storeNum_ok c (len / 8) ((hw.of_rest r₂).of_rest r₃) (a := a) (q := q) (off := off + len % 8)
      (by rw [(r₂.trans r₃).gpr _ (by decide), hc]) (by simp [hq.1, hq.2]) ha (by omega) (by omega)
      (fun i hi => by
        rw [(r₂.trans r₃).wr, g₃, show off + len % 8 + i = off + (len % 8 + i) by omega]
        exact hout _ (by omega))
      (fun i hi => by
        rw [g₃, show off + len % 8 + i = off + (len % 8 + i) by omega]
        exact hsep _ (by omega)))
      fun s₄ ⟨r₄, m₄⟩ => ⟨(r₂.trans r₃).trans r₄, ?_⟩
    have hwa := writeBytes_append s.mem (s.gpr q + BitVec.ofNat 64 off) (beBytes (len % 8) (s₂.gpr .t0))
      (toBytes (8 * (len / 8)) (if c then wordsVal s.mem base a (len / 8) else 0)) (by
        rw [hB, VG.Proof.Weierstrass.length_toBytes]; omega)
    rw [hB, add_ofNat_add] at hwa
    rw [m₄, mem₃, g₃, g₂, m₂]
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hwa]
    congr 1
    have hl : toBytes len = toBytes (len % 8 + 8 * (len / 8)) := by congr 1; omega
    rw [v₂, beBytes_toBytes, wordsVal_top, hl, toBytes_add]
    have hX := wordsVal_lt s.mem base a (len / 8)
    cases c
    · simp [maskOf]
    · simp only [maskOf, ↓reduceIte, BitVec.and_allOnes]
      have e1 : (wordsVal s.mem base a (len / 8) + 2 ^ (64 * (len / 8)) *
          (word s.mem base (a + 8 * (len / 8))).toNat) >>> (8 * (8 * (len / 8))) =
          (word s.mem base (a + 8 * (len / 8))).toNat := by
        rw [Nat.shiftRight_eq_div_pow, show 8 * (8 * (len / 8)) = 64 * (len / 8) by omega,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hX, Nat.zero_add]
      rw [e1, show 2 ^ (64 * (len / 8)) = 2 ^ (8 * (8 * (len / 8))) by congr 1; omega, toBytes_mod]

/-- `loadLen` of whole words is `loadNum`. -/
theorem loadLen_mul (n o : Nat) (p : Reg) (off : Nat) : loadLen (8 * n) o p off = loadNum n o p off := by
  simp [loadLen]

/-- `storeLen` of whole words is `storeNum`. -/
theorem storeLen_mul (n a : Nat) (q : Reg) (off : Nat) : storeLen (8 * n) a q off = storeNum n a q off := by
  simp [storeLen]

/-- The mask of a byte being `04`. -/
theorem lead_mask (b : BitVec 8) :
    (0 : BitVec 64) - (((b.setWidth 64 ^^^ BitVec.ofInt 64 4) + BitVec.ofInt 64 (-1)) >>> 63) = maskOf (decide (b = 4)) := by
  revert b; decide

/-- `leadMask q`: `a7` is the mask of the byte at `[q]` being `04`. -/
theorem leadMask_ok {s : State} {q : Reg}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr q) 1) :
    WP isa (.block (leadMask q)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧ s'.gpr .a7 = maskOf (decide (s.mem (s.gpr q) = 4)) := by
  rw [leadMask]
  refine wp_lbu (off := 0) (by decide) (by simp) hin fun s₁ u₁ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  refine WP.cons (exec_addi (by decide)) ?_
  refine wp_srl (by decide) fun s₂ u₂ => wp_li (imm := 0) (by decide) fun s₃ u₃ => wp_sub fun s₄ u₄ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · exact ((u₁.rest (by decide)).trans ((((Upd.write _ _ _).rest (ws := [.t0]) (by decide)).app
      ((Upd.write _ _ _).rest (ws := [.t0]) (by decide))).mono (by decide)) |>.trans
      ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans (u₄.rest (by decide)))))
  · rw [u₄.mem, u₃.mem, u₂.mem]; exact u₁.mem
  · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr]
    simp only [State.write, ↓reduceIte]
    rw [u₁.gpr, show BitVec.ofNat 64 0 = 0 from rfl, lead_mask]

end VG.Proof.Weierstrass.RISCV64
