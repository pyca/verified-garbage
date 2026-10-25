module

public import VerifiedGarbage.Impl.Gather.PPC64LE
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Buffer
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Gathering a list of slices, PPC64LE: copying a slice

`copyWords` copies `k ≥ 1` doublewords from `r3` to `r9` through `r0`
(`copyWords_wp`), `copyBytes` `n ≥ 1` bytes (`copyBytes_wp`), and
`copySlice` the `n` bytes at `r3` to `r9`: its whole doublewords, then its
last `n mod 8` bytes, leaving `r9` past them (`copySlice_wp`). The bytes
copied and the bytes written do not overlap. As on AArch64
(`Proof/AesGcm/AArch64/Gather/Copy.lean`).
-/

@[expose] public section

namespace VG.Proof.Gather.PPC64LE

open VG VG.PPC64LE VG.Impl.Gather.PPC64LE VG.WriteBytes
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_ld wp_std wp_lbz wp_stb wp_addi wp_subi wp_lsr wp_li
  wp_and)
open VG.Spec.Aes (bytesAt)

/-- The registers the copy of a slice writes. -/
abbrev copyRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r9]

/-- What the copy of a slice keeps: the other registers, the stack pointer,
the link register and the permissions. -/
structure Keeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ copyRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  lr : t.lr = s.lr
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h₁ : Keeps s t) (h₂ : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.lr.trans h₁.lr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem kU {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v) (hd : d ∈ copyRegs := by decide) :
    Keeps s t :=
  ⟨fun r hr => u.other r fun e => hr (e ▸ hd), u.sp, u.lr, u.rd, u.wr⟩

theorem kM {s t : State} {m : Mem} (u : Mupd s t m) : Keeps s t :=
  ⟨fun r _ => by rw [u.gpr], u.sp, u.lr, u.rd, u.wr⟩

/-! ## Regions -/

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩

theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-! ## Memory -/

/-- The byte at `S + j + i` (`i < n`), not among the `j` bytes written at
`D`, is what it was. -/
theorem byte_kept {m : Mem} {S D : Addr} {j n L : Nat} (hd : (⟨S, L⟩ : Region).Disjoint ⟨D, L⟩)
    (hj : j + n ≤ L) (hL : L < 2 ^ 64) {i : Nat} (hi : i < n) :
    writeBytes m D (bytesAt m S j) (S + BitVec.ofNat 64 j + BitVec.ofNat 64 i) =
      m (S + BitVec.ofNat 64 j + BitVec.ofNat 64 i) := by
  refine (writeBytes_frame m D (bytesAt m S j) (R := ⟨D, j⟩)
    (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  rw [Offset.add_ofNat_add_ofNat] at hcon
  exact hd _ (Offset.contains_base S (show j + i + 1 ≤ L by omega_arith) (by omega_arith))
    (Region.sub_prefix (show j ≤ L by omega_arith) _ hcon)

theorem readW_kept {m : Mem} {S D : Addr} {j L : Nat} (hd : (⟨S, L⟩ : Region).Disjoint ⟨D, L⟩)
    (hj : j + 8 ≤ L) (hL : L < 2 ^ 64) :
    (writeBytes m D (bytesAt m S j)).readW (S + BitVec.ofNat 64 j) 64 = m.readW (S + BitVec.ofNat 64 j) 64 :=
  Mem.readW_congr fun i hi => byte_kept hd hj hL (n := 8) (by simpa using hi)

/-- A doubleword copied is its bytes copied. -/
theorem writeW_readW (m m' : Mem) (D S : Addr) :
    m'.writeW D (m.readW S 64) = writeBytes m' D (bytesAt m S 8) := by
  rw [show m'.writeW D (m.readW S 64) = m'.write D 8 (m.read S 8) by simp [Mem.writeW, Mem.readW],
    write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  exact Mem.extractLsb'_read m S hj

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem byte_rt (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem eval_nonzero {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.nonzero .d r) s = some (decide (a ≠ 0)) := by
  rw [VG.Proof.Poly1305.PPC64LE.eval_nonzero, h]
  congr 1
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
  constructor
  · intro hx h0; subst h0; exact hx rfl
  · intro hx h0
    apply hx
    have := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this

theorem eval_zero {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .d r) s = some (decide (a = 0)) := by
  rw [VG.Proof.Poly1305.PPC64LE.eval_zero, h]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h0
    have := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this
  · intro h0; subst h0; rfl

theorem ofNat_sub_one {a : Nat} (h : 0 < a) : BitVec.ofNat 64 a - BitVec.ofNat 64 1 = BitVec.ofNat 64 (a - 1) :=
  Offset.ofNat_sub_ofNat h

/-! ## The doubleword loop -/

/-- What the doubleword loop needs: `k ≥ 1` doublewords at `S` to copy to
`D`, apart. -/
structure WordsPre (s : State) (S D : Addr) (k : Nat) : Prop where
  r3 : s.gpr .r3 = S
  r9 : s.gpr .r9 = D
  r5 : s.gpr .r5 = BitVec.ofNat 64 k
  pos : 1 ≤ k
  lt : 8 * k < 2 ^ 64
  rd : Covers [⟨S, 8 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 8 * k⟩] s.wr
  disj : (⟨S, 8 * k⟩ : Region).Disjoint ⟨D, 8 * k⟩

theorem copyWords_wp (s : State) {S D : Addr} {k : Nat} (h : WordsPre s S D k) :
    WP isa copyWords s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S (8 * k)) ∧
      s'.gpr .r3 = S + BitVec.ofNat 64 (8 * k) ∧ s'.gpr .r9 = D + BitVec.ofNat 64 (8 * k) ∧
      s'.gpr .r4 = s.gpr .r4 ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ t.gpr .r3 = S + BitVec.ofNat 64 (8 * i) ∧
      t.gpr .r9 = D + BitVec.ofNat 64 (8 * i) ∧ t.gpr .r5 = BitVec.ofNat 64 (k - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S (8 * i)) ∧ t.gpr .r4 = s.gpr .r4 ∧ Keeps s t) ?_ (k - 0) _
    ⟨0, rfl, h.pos, by rw [h.r3]; exact (BitVec.add_zero _).symm, by rw [h.r9]; exact (BitVec.add_zero _).symm,
      by rw [h.r5, Nat.sub_zero], by simp [bytesAt, writeBytes_nil], rfl, Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, r3, r9, r5, mem, r4, kp⟩
  have hin : 8 * i + 8 ≤ 8 * k := by omega_arith
  refine wp_ld (a := S + BitVec.ofNat 64 (8 * i)) (by decide) (by decide)
    (by rw [r3]; exact BitVec.add_zero _) (by rw [kp.rd, kp.wr]; exact in_off h.rd hin (by omega_arith))
    fun t₁ u₁ => ?_
  refine wp_std (a := D + BitVec.ofNat 64 (8 * i)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), r9]; exact BitVec.add_zero _)
    (by rw [u₁.wr, kp.wr]; exact in_off h.wr hin (by omega_arith)) fun t₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_subi (by decide) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have kp₅ : Keeps s t₅ := kp.trans ((kU u₁).trans ((kM u₂).trans ((kU u₃).trans ((kU u₄).trans (kU u₅)))))
  have hmem : t₅.mem = writeBytes s.mem D (bytesAt s.mem S (8 * (i + 1))) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, mem, readW_kept h.disj hin (by omega_arith),
      writeW_readW, show 8 * (i + 1) = 8 * i + 8 by omega_arith, Proof.Cmac.Stream.bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega_arith), Proof.Cmac.bytesAt_length]
  have hstep (P : Addr) : P + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 8 = P + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  have r3' : t₅.gpr .r3 = S + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), r3, hstep]
  have r9' : t₅.gpr .r9 = D + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r9, hstep]
  have r5' : t₅.gpr .r5 = BitVec.ofNat 64 (k - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r5,
      ofNat_sub_one (by omega_arith), Nat.sub_sub]
  have r4' : t₅.gpr .r4 = s.gpr .r4 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r4]
  have ev := eval_nonzero (r := .r5) (a := k - (i + 1)) r5' (by omega_arith)
  by_cases he : i + 1 = k
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [r3', he], by rw [r9', he], r4', kp₅⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, k - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r3', r9', r5', hmem, r4', kp₅⟩

/-! ## The byte loop -/

/-- What the byte loop needs: `n ≥ 1` bytes at `S` to copy to `D`, apart. -/
structure BytesPre (s : State) (S D : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = S
  r9 : s.gpr .r9 = D
  r4 : s.gpr .r4 = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

theorem copyBytes_wp (s : State) {S D : Addr} {n : Nat} (h : BytesPre s S D n) :
    WP isa copyBytes s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .r9 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa)
    (fun (w : Nat) (t : State) => ∃ i, w = n - i ∧ i < n ∧ t.gpr .r3 = S + BitVec.ofNat 64 i ∧
      t.gpr .r9 = D + BitVec.ofNat 64 i ∧ t.gpr .r4 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧ Keeps s t) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r3]; exact (BitVec.add_zero _).symm, by rw [h.r9]; exact (BitVec.add_zero _).symm,
      by rw [h.r4, Nat.sub_zero], by simp [bytesAt, writeBytes_nil], Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, r3, r9, r4, mem, kp⟩
  have hin : i + 1 ≤ n := by omega_arith
  refine wp_lbz (a := S + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [r3]; exact BitVec.add_zero _) (by rw [kp.rd, kp.wr]; exact in_off h.rd hin (by omega_arith))
    fun t₁ u₁ => ?_
  refine wp_stb (a := D + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), r9]; exact BitVec.add_zero _)
    (by rw [u₁.wr, kp.wr]; exact in_off h.wr hin (by omega_arith)) fun t₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_subi (by decide) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have kp₅ : Keeps s t₅ := kp.trans ((kU u₁).trans ((kM u₂).trans ((kU u₃).trans ((kU u₄).trans (kU u₅)))))
  have hb : t.mem (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) := by
    rw [mem]
    have := byte_kept (m := s.mem) (j := i) (n := 1) (i := 0) h.disj hin (by omega_arith) (by decide)
    rwa [BitVec.add_zero] at this
  have hmem : t₅.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, byte_rt, hb, mem, Proof.Cmac.Stream.bytesAt_append,
      bytesAt_one, writeBytes_snoc _ _ _ _ (by rw [Proof.Cmac.bytesAt_length]; omega_arith),
      Proof.Cmac.bytesAt_length]
  have hstep (P : Addr) : P + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = P + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have r3' : t₅.gpr .r3 = S + BitVec.ofNat 64 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), r3, hstep]
  have r9' : t₅.gpr .r9 = D + BitVec.ofNat 64 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r9, hstep]
  have r4' : t₅.gpr .r4 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r4,
      ofNat_sub_one (by omega_arith), Nat.sub_sub]
  have ev := eval_nonzero (r := .r4) (a := n - (i + 1)) r4' (by omega_arith)
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [r9', he], kp₅⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r3', r9', r4', hmem, kp₅⟩

/-! ## A slice -/

/-- What the copy of a slice needs: `n` bytes at `S` to copy to `D`, apart. -/
structure SlicePre (s : State) (S D : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = S
  r9 : s.gpr .r9 = D
  r4 : s.gpr .r4 = BitVec.ofNat 64 n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

theorem ofNat_lsr3 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

theorem ofNat_and7 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 7 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_arith),
    show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- `copySlice`: the `n` bytes at `S` to `D`, and `r9` past them. -/
theorem copySlice_wp (s : State) {S D : Addr} {n : Nat} (h : SlicePre s S D n) :
    WP isa copySlice s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .r9 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hn := h.lt
  have hqr : 8 * (n / 8) + n % 8 = n := Nat.div_add_mod n 8
  unfold copySlice wordsArg bytesArg
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have r5₁ : s₁.gpr .r5 = BitVec.ofNat 64 (n / 8) := by rw [u₁.gpr, h.r4, ofNat_lsr3 hn]
  have kp₁ := (kU u₁)
  -- The whole doublewords.
  have hblk : WP isa (.ite (.zero .d .r5) (.block []) copyWords) s₁ fun s₂ =>
      s₂.mem = writeBytes s.mem D (bytesAt s.mem S (8 * (n / 8))) ∧
      s₂.gpr .r3 = S + BitVec.ofNat 64 (8 * (n / 8)) ∧ s₂.gpr .r9 = D + BitVec.ofNat 64 (8 * (n / 8)) ∧
      s₂.gpr .r4 = BitVec.ofNat 64 n ∧ Keeps s s₂ := by
    refine WP.ite (decide (n / 8 = 0)) (eval_zero r5₁ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 8 = 0 := by simpa using ht
      refine WP.block_nil ⟨?_, ?_, ?_, ?_, kp₁⟩
      · rw [u₁.mem, h0, Nat.mul_zero]; simp [bytesAt, writeBytes_nil]
      · rw [u₁.other _ (by decide), h.r3, h0]; exact (BitVec.add_zero _).symm
      · rw [u₁.other _ (by decide), h.r9, h0]; exact (BitVec.add_zero _).symm
      · rw [u₁.other _ (by decide), h.r4]
    · have h0 : n / 8 ≠ 0 := by simpa using hf
      have hb : WordsPre s₁ S D (n / 8) :=
        ⟨by rw [u₁.other _ (by decide), h.r3], by rw [u₁.other _ (by decide), h.r9], r5₁, by omega_arith, by omega_arith,
          by rw [u₁.rd, u₁.wr]; exact covers_prefix h.rd (by omega_arith),
          by rw [u₁.wr]; exact covers_prefix h.wr (by omega_arith),
          (h.disj.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))⟩
      refine WP.mono (copyWords_wp s₁ hb) fun s₂ ⟨m₂, r3₂, r9₂, r4₂, kp₂⟩ => ⟨?_, r3₂, r9₂, ?_, kp₁.trans kp₂⟩
      · rw [m₂, u₁.mem]
      · rw [r4₂, u₁.other _ (by decide), h.r4]
  refine WP.seq (WP.mono hblk fun s₂ ⟨m₂, r3₂, r9₂, r4₂, kp₂⟩ => ?_)
  -- The last `n mod 8` bytes.
  refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => WP.block_nil ?_)
  have r4₄ : s₄.gpr .r4 = BitVec.ofNat 64 (n % 8) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₃.gpr, r4₂, ofNat_and7 hn]
  have kp₄ : Keeps s s₄ := kp₂.trans ((kU u₃).trans (kU u₄))
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hS : (⟨S + BitVec.ofNat 64 (8 * (n / 8)), n % 8⟩ : Region).Sub ⟨S, n⟩ := Offset.sub_base _ (by omega_arith)
  have hD : (⟨D + BitVec.ofNat 64 (8 * (n / 8)), n % 8⟩ : Region).Sub ⟨D, n⟩ := Offset.sub_base _ (by omega_arith)
  have hlen : (bytesAt s.mem S (8 * (n / 8))).length = 8 * (n / 8) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes still to copy are what they were.
  have hrest : bytesAt s₄.mem (S + BitVec.ofNat 64 (8 * (n / 8))) (n % 8) =
      bytesAt s.mem (S + BitVec.ofNat 64 (8 * (n / 8))) (n % 8) := by
    rw [m₄, m₂]
    refine bytesAt_frame (writeBytes_frame s.mem D _ (R := ⟨D, 8 * (n / 8)⟩)
      (by rw [hlen]; exact Region.contains_self _ _)) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.disj.sub_left hS).sub_right (Region.sub_prefix (by omega_arith))
  have hend : D + BitVec.ofNat 64 (8 * (n / 8)) + BitVec.ofNat 64 (n % 8) = D + BitVec.ofNat 64 n := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hqr]
  have hall : writeBytes (writeBytes s.mem D (bytesAt s.mem S (8 * (n / 8)))) (D + BitVec.ofNat 64 (8 * (n / 8)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (8 * (n / 8))) (n % 8)) = writeBytes s.mem D (bytesAt s.mem S n) := by
    have e := writeBytes_append s.mem D (bytesAt s.mem S (8 * (n / 8)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (8 * (n / 8))) (n % 8))
      (by rw [hlen, Proof.Cmac.bytesAt_length]; omega_arith)
    rw [hlen] at e
    rw [e, ← Proof.Cmac.Stream.bytesAt_append, hqr]
  refine WP.ite (decide (n % 8 = 0)) (eval_zero r4₄ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 8 = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, ?_, kp₄⟩
    · rw [m₄, m₂, ← hall, h0]; simp [bytesAt, writeBytes_nil]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), r9₂, ← hend, h0]; exact (BitVec.add_zero _).symm
  · have h0 : n % 8 ≠ 0 := by simpa using hf
    have bp : BytesPre s₄ (S + BitVec.ofNat 64 (8 * (n / 8))) (D + BitVec.ofNat 64 (8 * (n / 8))) (n % 8) :=
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), r3₂],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), r9₂], r4₄, by omega_arith, by omega_arith,
        by rw [kp₄.rd, kp₄.wr]; exact covers_off h.rd (by omega_arith) hn,
        by rw [kp₄.wr]; exact covers_off h.wr (by omega_arith) hn, (h.disj.sub_left hS).sub_right hD⟩
    refine WP.mono (copyBytes_wp s₄ bp) fun s₅ ⟨m₅, r9₅, kp₅⟩ => ⟨?_, by rw [r9₅, hend], kp₄.trans kp₅⟩
    rw [m₅, hrest, m₄, m₂, hall]

end VG.Proof.Gather.PPC64LE
