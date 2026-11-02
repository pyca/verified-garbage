module

public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Numbers of `8 k + 4` bytes to and from slots on RISC-V

P-224's numbers are 28 bytes: `loadNum4` reads the top word from four bytes
(`be32_toNat`: a big-endian word is its bytes), then the rest by `loadNum`
(`loadNum4_ok`); `storeNum4` writes the top word's low four bytes (`toBytes`
of the word, `beBytes4_eq`), then the rest by `storeNum` (`storeNum4_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Mont
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.RISCV64.ByteLoad (beWord beBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.Spec.Weierstrass (ofBytes toBytes)

/-- A big-endian word is its four bytes. -/
theorem be32_toNat (m : Mem) (p : Addr) (off : Nat) :
    ((beWord m p off).setWidth 64).toNat = ofBytes (bytesAt m (p + BitVec.ofNat 64 off) 4) := by
  rw [show bytesAt m (p + BitVec.ofNat 64 off) 4 = [m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 0),
      m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 off + BitVec.ofNat 64 3)] from rfl]
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (beWord m p off).isLt (by decide))]
  simp only [add_ofNat_add, Nat.add_zero, beWord, BitVec.toNat_append, shl8_or, ofBytes, List.foldl_cons,
    List.foldl_nil]
  omega

/-- `storeBE 4`'s bytes are `toBytes 4`. -/
theorem beBytes4_eq (v : BitVec 64) : beBytes 4 v = toBytes 4 v.toNat := by
  simp only [beBytes, toBytes]
  rw [show (List.range 4).reverse = (List.range 4).map (fun j => 4 - 1 - j) from rfl, List.map_map]
  apply List.map_congr_left
  intro j _
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]

/-- Four bytes of a region. -/
theorem in_rd4 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 4 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 4 :=
  ⟨_, hr, Offset.contains_base p ho (by omega)⟩

/-- `loadNum4`: the `8 k + 4` bytes at `p + off`, big-endian, to the slot at `o`. -/
theorem loadNum4_ok (k : Nat) {s : State} {base : Addr} {o : Nat} {p : Reg} {off : Nat}
    (hw : WsReg s base) (hp : p ∉ [Reg.t0, .t1]) (ho : o % 8 = 0) (ho' : o + 8 * (k + 1) ≤ 2048)
    (hoff : off + 4 + 8 * k ≤ 2048)
    (hin4 : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 4)
    (hin : ∀ j < k, InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 (off + 4 + 8 * j)) 8)
    (hsep : ∀ i < 4 + 8 * k, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (loadNum4 k o p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * (k + 1)) s.mem s'.mem ∧
      wordsVal s'.mem base o (k + 1) = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) (4 + 8 * k)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
  rw [loadNum4, List.append_assoc]
  refine WP.block_append (WP.mono (VG.RISCV64.ByteLoad.loadBE32_ok (d := .t0) (tmp := .t1) (n := p) (off := off)
    (Ne.symm hp.1) (Ne.symm hp.2) (by decide) (by omega) hin4) fun s₁ e₁ => ?_)
  subst e₁
  have r₁ : Rest [.t0, .t1] s ((s.write .t1 ((s.mem (s.gpr p + BitVec.ofNat 64 (off + 3))).setWidth 64)).write .t0
      ((beWord s.mem (s.gpr p) off).setWidth 64)) :=
    ((Upd.write _ _ _).rest (by decide)).trans ((Upd.write _ _ _).rest (by decide))
  have hw₁ := hw.of_rest r₁
  refine sd_ws hw₁ (d := o + 8 * k) (by omega) (by omega) fun s₂ u₂ => ?_
  have r₂ : Rest [.t0, .t1] s s₂ := r₁.trans (u₂.rest _)
  have O₂ : Outside base (o + 8 * k) 8 s.mem s₂.mem := by
    rw [u₂.mem]; exact writeW_outside _ _ _ (by omega)
  have g₂ : s₂.gpr p = s.gpr p := r₂.gpr _ (by simp [hp.1, hp.2])
  refine WP.mono (loadNum_ok k (hw.of_rest r₂) (p := p) (off := off + 4) (by simp [hp.1, hp.2]) ho (by omega)
    (by omega) (fun j hj => by
      rw [r₂.rd, r₂.wr, g₂]
      exact hin j hj)
    (fun i hi => by
      rw [g₂, show off + 4 + i = off + (4 + i) by omega]
      exact hsep _ (by omega)))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ⟨r₂.trans r₃, (O₂.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega)), ?_⟩
  have e₃' : wordsVal s₃.mem base o k = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 (off + 4)) (8 * k)) := by
    rw [e₃, g₂, bytesAt_out O₂ (by omega) (fun i hi => by
      rw [add_ofNat_add, show off + 4 + i = off + (4 + i) by omega]; exact hsep (4 + i) (by omega))]
  rw [wordsVal_top, e₃', O₃.word (by omega) (by omega), u₂.mem, word_writeW_self]
  simp only [State.write, ↓reduceIte]
  rw [be32_toNat, bytesAt_add, ofBytes_append, length_bytesAt, add_ofNat_add,
    show (256 : Nat) ^ (8 * k) = 2 ^ (64 * k) by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
  rw [Nat.mul_comm (2 ^ (64 * k))]
  omega

open VG.WriteBytes in
/-- `storeNum4`: the slot's number under the mask, or zeros, big-endian in
`8 k + 4` bytes at `q + off`. -/
theorem storeNum4_ok (c : Bool) (k : Nat) {s : State} {base : Addr} {a : Nat} {q : Reg} {off : Nat}
    (hw : WsReg s base) (hc : s.gpr .a7 = maskOf c) (hq : q ∉ [Reg.t0, .t1]) (ha : a % 8 = 0)
    (ha' : a + 8 * (k + 1) ≤ 2048) (hoff : off + 4 + 8 * k ≤ 2048)
    (hout : ∀ i < 4 + 8 * k, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + i)) 1)
    (hsep : ∀ i < 4 + 8 * k, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (storeNum4 k a q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes (4 + 8 * k) (if c then wordsVal s.mem base a (k + 1) else 0)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [storeNum4, List.cons_append, List.append_assoc]
  refine ld_ws hw (d := a + 8 * k) (by omega) (by omega) fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  have r₂ : Rest [.t0, .t1] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have g₂ : s₂.gpr q = s.gpr q := r₂.gpr _ (by simp [hq.1, hq.2])
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have v₂ : s₂.gpr .t0 = word s.mem base (a + 8 * k) &&& maskOf c := by
    rw [u₂.gpr, u₁.gpr, u₁.other .a7 (by decide), hc]
  rw [List.nil_append]
  refine WP.block_append (WP.mono (VG.RISCV64.ByteLoad.storeBE_ok (s := s₂) (v := .t0) (tmp := .t1) (n := q)
    (off := off) (w := 4) (by decide) (Ne.symm hq.2) (by decide) (by decide) (by omega) (fun j hj => by
      rw [r₂.wr, g₂]; exact hout j (by omega))) fun s₃ e₃ => ?_)
  have hB : (beBytes 4 (s₂.gpr .t0)).length = 4 := VG.RISCV64.ByteLoad.beBytes_length _ _
  have U₃ := writeBytes_unch (base := base) (Q := s.gpr q + BitVec.ofNat 64 off) (xs := beBytes 4 (s₂.gpr .t0))
    s.mem (fun i hi => by rw [hB] at hi; rw [add_ofNat_add]; exact hsep i (by omega))
  have mem₃ : s₃.mem = writeBytes s₂.mem (s₂.gpr q + BitVec.ofNat 64 off) (beBytes 4 (s₂.gpr .t0)) := by
    rw [e₃]; rfl
  have r₃ : Rest [.t0, .t1] s₂ s₃ := ⟨fun r hr => by
    have : r ≠ .t1 := fun h => hr (by simp [h])
    rw [e₃]; simp only [State.write, this, ↓reduceIte], by rw [e₃]; rfl, by rw [e₃]; rfl, by rw [e₃]; rfl⟩
  have g₃ : s₃.gpr q = s.gpr q := (r₂.trans r₃).gpr _ (by simp [hq.1, hq.2])
  refine WP.mono (storeNum_ok c k ((hw.of_rest r₂).of_rest r₃) (a := a) (q := q) (off := off + 4)
    (by rw [(r₂.trans r₃).gpr _ (by decide), hc]) (by simp [hq.1, hq.2]) ha
    (by omega) (by omega)
    (fun i hi => by
      rw [(r₂.trans r₃).wr, g₃, show off + 4 + i = off + (4 + i) by omega]
      exact hout _ (by omega))
    (fun i hi => by
      rw [g₃, show off + 4 + i = off + (4 + i) by omega]
      exact hsep _ (by omega)))
    fun s₄ ⟨r₄, m₄⟩ => ⟨(r₂.trans r₃).trans r₄, ?_⟩
  have hwa := writeBytes_append s.mem (s.gpr q + BitVec.ofNat 64 off) (beBytes 4 (s₂.gpr .t0))
    (toBytes (8 * k) (if c then wordsVal s.mem base a k else 0)) (by
      rw [hB, VG.Proof.Weierstrass.length_toBytes]; omega)
  rw [hB, add_ofNat_add] at hwa
  rw [m₄, mem₃, g₃, g₂, m₂]
  rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hwa]
  congr 1
  rw [v₂, beBytes4_eq, wordsVal_top, toBytes_add]
  have hX := wordsVal_lt s.mem base a k
  cases c
  · simp [maskOf]
  · simp only [maskOf, ↓reduceIte, BitVec.and_allOnes]
    have e1 : (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) >>> (8 * (8 * k)) =
        (word s.mem base (a + 8 * k)).toNat := by
      rw [Nat.shiftRight_eq_div_pow, show 8 * (8 * k) = 64 * k by omega, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hX, Nat.zero_add]
    rw [e1, show 2 ^ (64 * k) = 2 ^ (8 * (8 * k)) by congr 1; omega, toBytes_mod]

end VG.Proof.Weierstrass.RISCV64
