module

public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.AesCcm.Words

/-!
# AES-CCM on RISC-V: copying and XORing bytes

Untrusted: everything here is checked by Lean. `copy` copies `n ≥ 1` bytes
at `S` to `D` (`copy_wp`), and `xorBytes` XORs them into those at `D`
(`xorBytes_wp`), as on PPC64LE (`Proof/AesCcm/PPC64LE/Wp.lean`); and
arithmetic on lengths: shifts, and `sltu`.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- The registers `copy` and `xorBytes` write. -/
abbrev copyRegs : List Reg := [.t0, .t1, .a0, .a1, .a2]

/-- What `copy` and `xorBytes` keep: the other registers, the stack pointer
and the permissions. -/
structure Keeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ copyRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h₁ : Keeps s t) (h₂ : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem kU {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v) (hd : d ∈ copyRegs := by decide) :
    Keeps s t :=
  ⟨fun r hr => u.other r fun e => hr (e ▸ hd), u.sp, u.rd, u.wr⟩

theorem kM {s t : State} {m : Mem} (u : Mupd s t m) : Keeps s t :=
  ⟨fun r _ => by rw [u.gpr], u.sp, u.rd, u.wr⟩

theorem PK.ofKeeps {s t : State} (h : Keeps s t) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (by
    simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩

/-! ## Memory -/

theorem in_off' {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n := by
  refine h _ _ ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The byte at `S + i` (`j ≤ i < L`), not among the `j` bytes written at
`D`, is what it was. -/
theorem byte_kept {m : Mem} {S D : Addr} {j L : Nat} (hd : (⟨S, L⟩ : Region).Disjoint ⟨D, L⟩)
    (hL : L < 2 ^ 64) {i : Nat} (hi : i < L) (hj : j ≤ L) :
    writeBytes m D (bytesAt m S j) (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) := by
  refine (writeBytes_frame m D (bytesAt m S j) (R := ⟨D, j⟩)
    (by rw [length_bytesAt]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hd _ (Offset.contains_base S (show i + 1 ≤ L by omega) (by omega)) (Region.sub_prefix hj _ hcon)

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem byte_rt (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_sub_one {a : Nat} (h : 0 < a) : BitVec.ofNat 64 a - BitVec.ofNat 64 1 = BitVec.ofNat 64 (a - 1) :=
  Offset.ofNat_sub_ofNat h

theorem eval_nz {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.nonzero r) s = some (decide (a ≠ 0)) :=
  eval_nonzero_ofNat s r ha h

theorem eval_z {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero r) s = some (decide (a = 0)) :=
  eval_zero_ofNat s r ha h

/-! ## Copying bytes -/

/-- What the byte loops need: `n ≥ 1` bytes at `S` (`a0`) to copy or XOR
to `D` (`a1`), apart; `a2` is `n`. -/
structure BytesPre (s : State) (S D : Addr) (n : Nat) : Prop where
  a0 : s.gpr .a0 = S
  a1 : s.gpr .a1 = D
  a2 : s.gpr .a2 = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

theorem copy_wp (s : State) {S D : Addr} {n : Nat} (h : BytesPre s S D n) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .a1 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ i, w = n - i ∧ i < n ∧ t.gpr .a0 = S + BitVec.ofNat 64 i ∧
      t.gpr .a1 = D + BitVec.ofNat 64 i ∧ t.gpr .a2 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧ Keeps s t) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.a0]; exact (BitVec.add_zero _).symm, by rw [h.a1]; exact (BitVec.add_zero _).symm,
      by rw [h.a2, Nat.sub_zero], by simp [bytesAt, writeBytes_nil], Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, a0, a1, a2, mem, kp⟩
  have hin : i + 1 ≤ n := by omega
  refine wp_lbu (a := S + BitVec.ofNat 64 i) (by decide)
    (by rw [a0]; exact BitVec.add_zero _) (by rw [kp.rd, kp.wr]; exact in_off' h.rd hin hL)
    fun t₁ u₁ => ?_
  refine wp_sb (a := D + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), a1]; exact BitVec.add_zero _)
    (by rw [u₁.wr, kp.wr]; exact in_off' h.wr hin hL) fun t₂ u₂ => ?_
  refine wp_addi (by decide) fun t₃ u₃ => wp_addi (by decide) fun t₄ u₄ =>
    wp_subi (by decide) fun t₅ u₅ => WP.block_nil ?_
  have kp₅ : Keeps s t₅ := kp.trans ((kU u₁).trans ((kM u₂).trans ((kU u₃).trans ((kU u₄).trans (kU u₅)))))
  have hb : t.mem (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) := by
    rw [mem]; exact byte_kept h.disj hL hi (Nat.le_of_lt hi)
  have hmem : t₅.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, byte_rt, hb, mem, Proof.Cmac.Stream.bytesAt_append,
      bytesAt_one, writeBytes_snoc _ _ _ _ (by rw [length_bytesAt]; omega), length_bytesAt]
  have hstep (P : Addr) : P + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = P + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have a0' : t₅.gpr .a0 = S + BitVec.ofNat 64 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), a0, hstep]
  have a1' : t₅.gpr .a1 = D + BitVec.ofNat 64 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), a1, hstep]
  have a2' : t₅.gpr .a2 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), a2,
      ofNat_sub_one (by omega), Nat.sub_sub]
  have ev := eval_nz (r := .a2) (a := n - (i + 1)) a2' (by omega)
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [a1', he], kp₅⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, a0', a1', a2', hmem, kp₅⟩

/-! ## XORing bytes -/

/-- The bytes `d` XORed with `k`, byte by byte. -/
abbrev xorL (d k : List Byte) : List Byte := List.zipWith (· ^^^ ·) d k

theorem xor_byte (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 : Byte) = b ^^^ a := by
  rw [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.xor_comm]

theorem xorBytes_wp (s : State) {S D : Addr} {n : Nat} (h : BytesPre s S D n) :
    WP isa xorBytes s fun s' =>
      s'.mem = writeBytes s.mem D (xorL (bytesAt s.mem D n) (bytesAt s.mem S n)) ∧
      s'.gpr .a1 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ i, w = n - i ∧ i < n ∧ t.gpr .a0 = S + BitVec.ofNat 64 i ∧
      t.gpr .a1 = D + BitVec.ofNat 64 i ∧ t.gpr .a2 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (xorL (bytesAt s.mem D i) (bytesAt s.mem S i)) ∧ Keeps s t) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.a0]; exact (BitVec.add_zero _).symm, by rw [h.a1]; exact (BitVec.add_zero _).symm,
      by rw [h.a2, Nat.sub_zero], by simp [bytesAt, writeBytes_nil], Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, a0, a1, a2, mem, kp⟩
  have hin : i + 1 ≤ n := by omega
  have hlen : (xorL (bytesAt s.mem D i) (bytesAt s.mem S i)).length = i := by
    simp [length_bytesAt]
  refine wp_lbu (a := S + BitVec.ofNat 64 i) (by decide)
    (by rw [a0]; exact BitVec.add_zero _) (by rw [kp.rd, kp.wr]; exact in_off' h.rd hin hL)
    fun t₁ u₁ => ?_
  refine wp_lbu (a := D + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), a1]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr, kp.rd, kp.wr]; exact in_off' (VG.Covers.right h.wr) hin hL)
    fun t₂ u₂ => ?_
  refine wp_xor fun t₃ u₃ => ?_
  refine wp_sb (a := D + BitVec.ofNat 64 i) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), a1];
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr, kp.wr]; exact in_off' h.wr hin hL) fun t₄ u₄ => ?_
  refine wp_addi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ =>
    wp_subi (by decide) fun t₇ u₇ => WP.block_nil ?_
  have kp₇ : Keeps s t₇ := kp.trans ((kU u₁).trans ((kU u₂).trans ((kU u₃).trans ((kM u₄).trans
    ((kU u₅).trans ((kU u₆).trans (kU u₇)))))))
  -- The bytes read are what they were.
  have hS : t.mem (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) := by
    rw [mem]
    refine (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _))
      _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact h.disj _ (Offset.contains_base S (show i + 1 ≤ n by omega) (by omega))
      (Region.sub_prefix (show i ≤ n by omega) _ hc)
  have hD : t.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := by
    rw [mem]
    refine (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _))
      _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
    rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)] at hc
    omega
  have hmem : t₇.mem = writeBytes s.mem D (xorL (bytesAt s.mem D (i + 1)) (bytesAt s.mem S (i + 1))) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other .t0 (by decide),
      u₁.gpr, u₂.mem, u₁.mem, xor_byte, hS, hD, mem, Proof.Cmac.Stream.bytesAt_append,
      Proof.Cmac.Stream.bytesAt_append, xorL, xorL, List.zipWith_append (by simp [length_bytesAt]),
      bytesAt_one, bytesAt_one, List.zipWith_cons_cons, List.zipWith_nil_left,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
  have hstep (P : Addr) : P + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = P + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have a0' : t₇.gpr .a0 = S + BitVec.ofNat 64 (i + 1) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), a0, hstep]
  have a1' : t₇.gpr .a1 = D + BitVec.ofNat 64 (i + 1) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), a1, hstep]
  have a2' : t₇.gpr .a2 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), a2, ofNat_sub_one (by omega), Nat.sub_sub]
  have ev := eval_nz (r := .a2) (a := n - (i + 1)) a2' (by omega)
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [a1', he], kp₇⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, a0', a1', a2', hmem, kp₇⟩


/-! ## Big-endian doublewords -/

/-- `storeBE 8` stores the bytes of the byte-reversed word, least
significant first. -/
theorem beBytes_eq (x : BitVec 64) : ByteLoad.beBytes 8 x = Proof.Cmac.le8 (byteRev64 x) := by
  simp only [ByteLoad.beBytes, Proof.Cmac.le8]
  refine List.map_congr_left fun j hj => ?_
  have hj8 : j < 8 := List.mem_range.mp hj
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', byteRev64_getLsbD _ (by omega),
    BitVec.getLsbD_ushiftRight]
  simp only [hi, decide_true, Bool.true_and]
  congr 1
  omega

/-- What `storeBE 8` writes is the byte-reversed word. -/
theorem writeBytes_beBytes (m : Mem) (a : Addr) (x : BitVec 64) :
    writeBytes m a (ByteLoad.beBytes 8 x) = m.writeW a (byteRev64 x) := by
  rw [beBytes_eq, Proof.AesCcm.writeW64_eq]

/-- What `loadBE64` loads is the byte-reversed doubleword. -/
theorem be64_eq (m : Mem) (p : Addr) (off : Nat) :
    ByteLoad.be64 m p off = byteRev64 (m.readW (p + BitVec.ofNat 64 off) 64) := by
  have e : ∀ k, p + BitVec.ofNat 64 (off + k) = p + BitVec.ofNat 64 off + BitVec.ofNat 64 k := fun k => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have o : ∀ k, p + BitVec.ofNat 64 off + BitVec.ofNat 64 (k + 1) = p + BitVec.ofNat 64 off + BitVec.ofNat 64 k + 1 :=
    fun k => by rw [BitVec.add_assoc (p + _), BitVec.ofNat_add]; rfl
  rw [byteRev64_readW]
  simp only [ByteLoad.be64, e, o, BitVec.add_zero]

/-! ## Arithmetic on lengths -/

theorem ofNat_lsr {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

theorem ofNat_lsr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) :=
  ofNat_lsr hn

/-- `sltu` of two numbers. -/
theorem ofNat_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have e : (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (e.mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h)]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h (e.mp h'))), ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

end VG.Proof.AesCcm.RISCV64
