module

import VerifiedGarbage.Proof.Pbkdf2.AArch64.Copy
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.Block

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: 16-byte copies and padding

What `Hash.copyW` and `Hash.padW` (`Impl/Pbkdf2/Md/AArch64.lean`) write:
the bytes of one region copied to another, 16 at a time through `x9` and
`x10` (`copyW_ok`, as `copy32_ok`), and the end of a `B + D`-byte message
after the outer block's digest (`padW_ok`, as `padLen_ok`), with `stp`
where it can.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.AArch64 (Shape)
open VG.Proof.MdStream.AArch64 (wp_ldr wp_str wp_ldr32 wp_str32 wp_movz add_ofNat Upd Mupd)
open VG.Proof.MdStream.AArch64.OneShot (wp_ldp wp_stp wp_stpB ofNat_add8 Upd2)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.Pbkdf2.AArch64 (cp32)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero bytesAt_add bytesAt_writeBytes_sep)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Spec.Sha256 (bytesAt)

/-- A 64-bit read is unchanged by a 64-bit write elsewhere. -/
theorem readW_writeW_sep {m : Mem} {a b : Addr} (v : BitVec 64) (h : Mem.Sep a 8 b 8) :
    (m.writeW b v).readW a 64 = m.readW a 64 := by
  simp only [Mem.readW, Mem.writeW]
  exact congrArg _ (Mem.read_write_sep h (by decide))

/-- One more 16-byte word copied from `A` to `B`, as two 64-bit words both
read before either is written. -/
theorem copy16_mem (m : Mem) (A B : Addr) (o : Nat) (h8 : o % 8 = 0)
    (hsep : Mem.Sep A (o + 16) B (o + 16)) (hlt : o + 16 < 2 ^ 64) :
    ((writeBytes m B (bytesAt m A o)).writeW (B + BitVec.ofNat 64 o)
        ((writeBytes m B (bytesAt m A o)).readW (A + BitVec.ofNat 64 o) 64)).writeW
      (B + BitVec.ofNat 64 o + 8) ((writeBytes m B (bytesAt m A o)).readW (A + BitVec.ofNat 64 o + 8) 64) =
      writeBytes m B (bytesAt m A (o + 16)) := by
  obtain ⟨q, rfl⟩ : ∃ q, o = 8 * q := ⟨o / 8, by omega_arith⟩
  have e1 := copy_mem m A B q 8 (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) (by omega_arith)
  have e2 := copy_mem m A B (q + 1) 8 (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) (by omega_arith)
  simp only [Nat.reduceMul] at e1 e2
  rw [show 8 * q + 8 = 8 * (q + 1) by omega_arith] at e1
  rw [show 8 * (q + 1) + 8 = 8 * q + 16 by omega_arith] at e2
  have sep : Mem.Sep (A + BitVec.ofNat 64 (8 * (q + 1))) 8 (B + BitVec.ofNat 64 (8 * q)) 8 := by
    intro x hx hy
    apply hsep x (by
      rw [show x - A = (x - (A + BitVec.ofNat 64 (8 * (q + 1)))) + BitVec.ofNat 64 (8 * (q + 1)) by
        rw [← BitVec.sub_sub, BitVec.sub_add_cancel], BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 8 * (q + 1) < 2 ^ 64 by omega_arith)]
      have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (8 * (q + 1)))).toNat + 8 * (q + 1)) (2 ^ 64)
      omega_arith)
    rw [show x - B = (x - (B + BitVec.ofNat 64 (8 * q))) + BitVec.ofNat 64 (8 * q) by
      rw [← BitVec.sub_sub, BitVec.sub_add_cancel], BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8 * q < 2 ^ 64 by omega_arith)]
    have := Nat.mod_le ((x - (B + BitVec.ofNat 64 (8 * q))).toNat + 8 * q) (2 ^ 64)
    omega_arith
  have e3 : (writeBytes m B (bytesAt m A (8 * q))).readW (A + BitVec.ofNat 64 (8 * q) + 8) 64 =
      (writeBytes m B (bytesAt m A (8 * (q + 1)))).readW (A + BitVec.ofNat 64 (8 * (q + 1))) 64 := by
    rw [← e1, ofNat_add8, show 8 * q + 8 = 8 * (q + 1) by omega_arith, readW_writeW_sep _ sep]
  rw [e3, e1, ofNat_add8, show 8 * q + 8 = 8 * (q + 1) by omega_arith, e2]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- The load half of `cp128`: 16 bytes at `a` into `x9` and `x10`. -/
theorem ld16_ok {src : Reg} {o : Nat} {a : Addr} (hs : src ≠ .x9) (ho : o % 8 = 0 ∧ o + 16 ≤ 32768)
    (ha : s.gpr src + BitVec.ofNat 64 o = a) (h₁ : InRegions (s.rd ++ s.wr) a 8)
    (h₂ : InRegions (s.rd ++ s.wr) (a + 8) 8)
    (k : ∀ s', Upd2 s s' .x9 .x10 (s.mem.readW a 64) (s.mem.readW (a + 8) 64) → WP isa (.block is) s' Q) :
    WP isa (.block ((if o ≤ 496 then ([.ldp .x9 .x10 src o] : List Instr)
      else [.ldr .x .x9 src o, .ldr .x .x10 src (o + 8)]) ++ is)) s Q := by
  split
  · exact wp_ldp (by decide) ⟨ho.1, by omega_arith⟩ ha h₁ h₂ k
  · simp only [List.cons_append, List.nil_append]
    refine wp_ldr ⟨ho.1, by omega_arith⟩ ha h₁ fun s₁ u₁ => ?_
    refine wp_ldr (a := a + 8) ⟨by omega_arith, by omega_arith⟩ (by rw [u₁.other _ hs, ← ha, ofNat_add8])
      (by rw [u₁.rd, u₁.wr]; exact h₂) fun s₂ u₂ => ?_
    exact k s₂ ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.mem],
      fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

/-- The store half of `cp128`: `x9` and `x10` to the 16 bytes at `a`. -/
theorem st16_ok {dst : Reg} {o : Nat} {a : Addr} (ho : o % 8 = 0 ∧ o + 16 ≤ 32768)
    (ha : s.gpr dst + BitVec.ofNat 64 o = a) (h₁ : InRegions s.wr a 8) (h₂ : InRegions s.wr (a + 8) 8)
    (k : ∀ s', Mupd s s' ((s.mem.writeW a (s.gpr .x9)).writeW (a + 8) (s.gpr .x10)) →
      WP isa (.block is) s' Q) :
    WP isa (.block ((if o ≤ 496 then ([.stp .x9 .x10 dst o] : List Instr)
      else [.str .x .x9 dst o, .str .x .x10 dst (o + 8)]) ++ is)) s Q := by
  split
  · exact wp_stp ⟨ho.1, by omega_arith⟩ ha h₁ h₂ k
  · simp only [List.cons_append, List.nil_append]
    refine wp_str ⟨ho.1, by omega_arith⟩ ha h₁ fun s₁ u₁ => ?_
    refine wp_str (a := a + 8) ⟨by omega_arith, by omega_arith⟩ (by rw [u₁.gpr, ← ha, ofNat_add8])
      (by rw [u₁.wr]; exact h₂) fun s₂ u₂ => ?_
    exact k s₂ ⟨by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.gpr, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

end

/-- `c` 16-byte words from `src + o₁` to `dst + o₂`. -/
theorem copy128_ok {src dst : Reg} (hs : src ≠ .x9 ∧ src ≠ .x10) (hd : dst ≠ .x9 ∧ dst ≠ .x10)
    (o₁ o₂ : Nat) (c : Nat) (h₁ : o₁ % 8 = 0 ∧ o₁ + 16 * c ≤ 32768) (h₂ : o₂ % 8 = 0 ∧ o₂ + 16 * c ≤ 32768) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < c, ∀ j < 2, InRegions (s.rd ++ s.wr)
      (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (16 * k + 8 * j)) 8) →
    (∀ k < c, ∀ j < 2, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (16 * k + 8 * j)) 8) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (16 * c) (s.gpr dst + BitVec.ofNat 64 o₂) (16 * c) →
    (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (16 * c)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range c).flatMap (Hash.cp128 src dst o₁ o₂) ++ rest)) s Q := by
  induction c with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ c ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨h₁.1, by omega_arith⟩ ⟨h₂.1, by omega_arith⟩ _ s Q (fun j hj => hin j (by omega_arith))
      (fun j hj => hout j (by omega_arith)) (fun x hx hy => hsep x (by omega_arith) (by omega_arith))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [Hash.cp128, List.append_assoc]
    have i0 := hin c (by omega_arith) 0 (by omega_arith)
    have i1 := hin c (by omega_arith) 1 (by omega_arith)
    have o0 := hout c (by omega_arith) 0 (by omega_arith)
    have o1 := hout c (by omega_arith) 1 (by omega_arith)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at i0 i1 o0 o1
    rw [add_ofNat] at i0 i1 o0 o1
    rw [← Nat.add_assoc, ← ofNat_add8] at i1 o1
    refine ld16_ok (a := s.gpr src + BitVec.ofNat 64 (o₁ + 16 * c)) hs.1 ⟨by omega_arith, by omega_arith⟩
      (by rw [g₁ _ hs.1 hs.2]) (by rw [rd₁, wr₁]; exact i0) (by rw [rd₁, wr₁]; exact i1) fun s₂ u₂ => ?_
    refine st16_ok (a := s.gpr dst + BitVec.ofNat 64 (o₂ + 16 * c)) ⟨by omega_arith, by omega_arith⟩
      (by rw [u₂.other _ hd.1 hd.2, g₁ _ hd.1 hd.2]) (by rw [u₂.wr, wr₁]; exact o0)
      (by rw [u₂.wr, wr₁]; exact o1) fun s₃ g₃ => k s₃
        (fun r h9 h10 => by rw [g₃.gpr, u₂.other r h9 h10, g₁ r h9 h10])
        (by rw [g₃.rd, u₂.rd, rd₁]) (by rw [g₃.wr, u₂.wr, wr₁]) (by rw [g₃.sp, u₂.sp, sp₁]) ?_
    rw [g₃.mem, u₂.gpr₁, u₂.gpr₂, u₂.mem, m₁, ← add_ofNat, ← add_ofNat, Nat.mul_succ]
    exact copy16_mem s.mem _ _ (16 * c) (by omega_arith) (by rwa [← Nat.mul_succ]) (by omega_arith)

/-- `copyW src so dst d n` writes the `n` bytes (a multiple of 4) at `src + so` to `dst + d`. -/
theorem copyW_ok {src dst : Reg} (hs : src ≠ .x9 ∧ src ≠ .x10) (hd : dst ≠ .x9 ∧ dst ≠ .x10)
    (wide : Bool) (o₁ o₂ n : Nat) (hn : n % 4 = 0) (h₁ : o₁ % 4 = 0 ∧ o₁ + n ≤ 4096 * 4) (h₂ : o₂ % 4 = 0 ∧ o₂ + n ≤ 4096 * 4)
    (rest : List Instr) (s : State) (Q : State → Prop)
    (hin : ∀ a w, 0 < w → a + w ≤ n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 a) w)
    (hout : ∀ a w, 0 < w → a + w ≤ n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 a) w)
    (hsep : Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) n (s.gpr dst + BitVec.ofNat 64 o₂) n)
    (k : ∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) n) → WP isa (.block rest) s' Q) :
    WP isa (.block (Hash.copyW wide src o₁ dst o₂ n ++ rest)) s Q := by
  unfold Hash.copyW
  split
  · rename_i h8
    simp only [List.append_assoc]
    refine copy128_ok hs hd o₁ o₂ (n / 16) ⟨h8.2.1, by omega_arith⟩ ⟨h8.2.2, by omega_arith⟩ _ s Q
      (fun j hj i hi => hin _ _ (by omega_arith) (by omega_arith)) (fun j hj i hi => hout _ _ (by omega_arith) (by omega_arith))
      (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    -- The 8 bytes after the 16-byte words, if any.
    have step8 : ∀ (rest' : List Instr) (t : State), (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) →
        t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
        t.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
          (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (16 * (n / 16))) →
        (∀ t', (∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr → t'.sp = s.sp →
          t'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
            (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (n / 8 * 8)) → WP isa (.block rest') t' Q) →
        WP isa (.block ((if n % 16 ≥ 8 then ([.ldr .x .x9 src (o₁ + 16 * (n / 16)),
          .str .x .x9 dst (o₂ + 16 * (n / 16))] : List Instr) else []) ++ rest')) t Q := by
      intro rest' t g rd wr sp m k'
      split
      · rename_i h8'
        simp only [List.cons_append, List.nil_append]
        refine wp_ldr (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (16 * (n / 16))) ⟨by omega, by omega⟩
          (by rw [g _ hs.1 hs.2, add_ofNat]) (by rw [rd, wr]; exact hin _ _ (by omega_arith) (by omega_arith)) fun t₁ u₁ => ?_
        refine wp_str (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (16 * (n / 16))) ⟨by omega, by omega⟩
          (by rw [u₁.other _ hd.1, g _ hd.1 hd.2, add_ofNat]) (by rw [u₁.wr, wr]; exact hout _ _ (by omega_arith) (by omega_arith))
          fun t₂ g₂ => k' t₂ (fun r h9 h10 => by rw [g₂.gpr, u₁.other r h9, g r h9 h10]) (by rw [g₂.rd, u₁.rd, rd])
            (by rw [g₂.wr, u₁.wr, wr]) (by rw [g₂.sp, u₁.sp, sp]) ?_
        rw [g₂.mem, u₁.gpr, u₁.mem, m, show 16 * (n / 16) = 8 * (2 * (n / 16)) by omega_arith,
          show n / 8 * 8 = 8 * (2 * (n / 16)) + 8 by omega_arith]
        exact copy_mem s.mem _ _ (2 * (n / 16)) 8 (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) (by omega_arith)
      · exact k' t g rd wr sp (by rw [m, show n / 8 * 8 = 16 * (n / 16) by omega_arith])
    refine step8 _ s₁ g₁ rd₁ wr₁ sp₁ m₁ fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
    split
    · rename_i h4
      obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 4 := ⟨(n - 4) / 4, by omega_arith⟩
      have e8 : (4 * q + 4) / 8 * 8 = 4 * q := by omega_arith
      have e4 : 4 * q + 4 - 4 = 4 * q := by omega_arith
      rw [e4]
      rw [e8] at m₂
      simp only [cp32, List.cons_append, Nat.mul_zero, Nat.add_zero, List.nil_append]
      refine wp_ldr32 (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * q)) ⟨by omega_arith, by omega_arith⟩
        (by rw [g₂ _ hs.1 hs.2, add_ofNat]) (by rw [rd₂, wr₂]; exact hin _ _ (by omega_arith) (by omega_arith)) fun s₃ u₃ => ?_
      refine wp_str32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * q)) ⟨by omega_arith, by omega_arith⟩
        (by rw [u₃.other _ hd.1, g₂ _ hd.1 hd.2, add_ofNat]) (by rw [u₃.wr, wr₂]; exact hout _ _ (by omega_arith) (by omega_arith))
        fun s₄ g₄ => k s₄ (fun r h9 h10 => by rw [g₄.gpr, u₃.other r h9, g₂ r h9 h10]) (by rw [g₄.rd, u₃.rd, rd₂])
          (by rw [g₄.wr, u₃.wr, wr₂]) (by rw [g₄.sp, u₃.sp, sp₂]) ?_
      rw [g₄.mem, u₃.gpr, u₃.mem, m₂, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
      exact copy_mem s.mem _ _ q 4 hsep (by omega_arith)
    · rename_i h4
      simp only [List.nil_append]
      exact k s₂ g₂ rd₂ wr₂ sp₂ (by rw [m₂, show n / 8 * 8 = n by omega_arith])
  · rename_i h8
    simp only [Hash.copy32]
    refine VG.Proof.Pbkdf2.AArch64.copy32_ok hs.1 hd.1 o₁ o₂ (n / 4) ⟨h₁.1, by omega_arith⟩ ⟨h₂.1, by omega_arith⟩ rest s Q
      (fun j hj => hin _ _ (by omega_arith) (by omega_arith)) (fun j hj => hout _ _ (by omega_arith) (by omega_arith))
      (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) fun s' g rd wr sp m => k s' (fun r h9 _ => g r h9) rd wr sp
        (by rw [m, show 4 * (n / 4) = n by omega_arith])

/-! ## Padding -/

theorem writeW_zero8 (m : Mem) (a : Addr) : m.writeW a (0 : BitVec 64) = writeBytes m a (List.replicate 8 0) :=
  Pbkdf2.Memory.writeW_bytes m a _ _ (by decide)

theorem writeW_80 (m : Mem) (a : Addr) :
    m.writeW a ((0x80 : BitVec 16).setWidth 64) = writeBytes m a ([0x80] ++ List.replicate 7 0) :=
  Pbkdf2.Memory.writeW_bytes m a _ _ (by decide)

/-- Two 8-byte runs of bytes are one 16-byte run. -/
theorem writeBytes_8_8 (m : Mem) (p : Addr) (a : Nat) (xs ys : List Byte) (hx : xs.length = 8) (hy : ys.length = 8) :
    writeBytes (writeBytes m (p + BitVec.ofNat 64 a) xs) (p + BitVec.ofNat 64 (a + 8)) ys =
      writeBytes m (p + BitVec.ofNat 64 a) (xs ++ ys) :=
  Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [hx, add_ofNat]) (by rw [hx, hy]; decide)

/-- `c` pairs of zeros (`x10`) stored at `[x21 + A + 16 k]`. -/
theorem zst_ok (A : Nat) (hA : A % 8 = 0) (c : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop) (p : Addr), s.gpr .x21 = p → s.gpr .x10 = 0 →
    (∀ a, A ≤ a → a + 8 ≤ A + 16 * c → InRegions s.wr (p + BitVec.ofNat 64 a) 8) →
    A + 16 * c ≤ 512 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 A) (List.replicate (16 * c) 0) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range c).map (fun k => Instr.stp .x10 .x10 .x21 (A + 16 * k)) ++ rest)) s Q := by
  induction c with
  | zero =>
    intro rest s Q p _ _ _ _ k
    exact k s rfl rfl rfl rfl (by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil])
  | succ c ih =>
    intro rest s Q p hbp hx hout hlt k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q p hbp hx (fun a h1 h2 => hout a h1 (by omega_arith)) (by omega_arith) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_stpB (b := p) ⟨by omega_arith, by omega_arith⟩ (by rw [g₁, hbp]) (by rw [wr₁]; exact hout _ (by omega_arith) (by omega_arith))
      (by rw [wr₁]; exact hout _ (by omega_arith) (by omega_arith)) fun s₂ g₂ => k s₂ (by rw [g₂.gpr, g₁])
        (by rw [g₂.rd, rd₁]) (by rw [g₂.wr, wr₁]) (by rw [g₂.sp, sp₁]) ?_
    have hl : (List.replicate (16 * c) (0 : Byte)).length + 16 < 2 ^ 64 := by
      rw [List.length_replicate]; omega_arith
    rw [g₂.mem, g₁, hx, m₁, writeW_zero8, writeW_zero8, writeBytes_8_8 _ _ _ _ _ (by rfl) (by rfl),
      Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simpa using hl),
      List.replicate_append_replicate, List.replicate_append_replicate, Nat.mul_succ]

/-- `padW` writes the rest of the block at `p` (`x21`) after its first `D`
bytes, which it keeps: the padding of a `B + D`-byte message, as `padLen`. -/
theorem padW_ok {H : Hash} {M : Md H.P.B H.P.N H.P.L} (hs : Shape M) (hok : M.lenOk (H.P.B + H.D))
    (hD4 : H.D % 4 = 0) (hB16 : H.P.B % 16 = 0) (hL : H.P.L = 8 ∨ H.P.L = 16) (hA : H.padA + 16 ≤ H.P.B)
    (hB : H.P.B ≤ 128) {s : State} {p : Addr} (hbp : s.gpr .x21 = p)
    (hbx : s.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = p + BitVec.ofNat 64 (H.P.B - H.P.L))
    (hw : ∀ a n, a + n ≤ H.P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → Frame [⟨p, H.P.B⟩] s.mem s'.mem →
      bytesAt s'.mem (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = M.tailPad H.D →
      bytesAt s'.mem p H.D = bytesAt s.mem p H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.padW ++ rest)) s Q := by
  have hAD : H.D + 4 ≤ H.padA := by simp only [Hash.padA]; omega_arith
  have hA16 : H.padA % 16 = 0 := by simp only [Hash.padA]; omega_arith
  have hAD' : H.padA ≤ H.D + 16 := by simp only [Hash.padA]; omega_arith
  -- The head: `0x80` and zeros from `D` up to `padA`, and zero in `x10`.
  have head : ∀ (rest' : List Instr),
      (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.gpr .x10 = 0 → s'.rd = s.rd → s'.wr = s.wr →
        s'.sp = s.sp →
        s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.padA - H.D - 1) 0) →
        WP isa (.block rest') s' Q) →
      WP isa (.block ((if H.D % 16 = 0 then
        ([.movz .x .x9 0x80 0, .movz .x .x10 0 0, .stp .x9 .x10 .x21 H.D] : List Instr)
        else Impl.Pbkdf2.AArch64.padFrom H.D H.padA ++ [.movz .x .x10 0 0]) ++ rest')) s Q := by
    intro rest' k'
    split
    · rename_i h16
      have e : H.padA - H.D - 1 = 15 := by simp only [Hash.padA]; omega_arith
      simp only [List.cons_append, List.nil_append]
      refine wp_movz fun s₁ u₁ => wp_movz fun s₂ u₂ => ?_
      refine wp_stpB (b := p) ⟨by omega_arith, by omega_arith⟩ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hbp])
        (by rw [u₂.wr, u₁.wr]; exact hw _ _ (by omega_arith)) (by rw [u₂.wr, u₁.wr]; exact hw _ _ (by omega_arith))
        fun s₃ g₃ => k' s₃ (fun r h9 h10 => by rw [g₃.gpr, u₂.other r h10, u₁.other r h9])
          (by rw [g₃.gpr, u₂.gpr]; rfl) (by rw [g₃.rd, u₂.rd, u₁.rd]) (by rw [g₃.wr, u₂.wr, u₁.wr])
          (by rw [g₃.sp, u₂.sp, u₁.sp]) ?_
      rw [g₃.mem, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₂.mem, u₁.mem, e,
        show ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0 from rfl, writeW_80, writeW_zero8,
        writeBytes_8_8 _ _ _ _ _ (by rfl) (by rfl)]
      rfl
    · rename_i h16
      rw [List.append_assoc]
      refine Pbkdf2.AArch64.padFrom_ok (a := H.D) (b := H.padA) hAD (by omega_arith) hD4 (by omega_arith) hbp
        (fun j hj => hw _ _ (by omega_arith)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
      simp only [List.cons_append, List.nil_append]
      refine wp_movz fun s₂ u₂ => k' s₂ (fun r h9 h10 => by rw [u₂.other r h10, g₁ r h9]) (by rw [u₂.gpr]; rfl)
        (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) (by rw [u₂.sp, sp₁]) (by rw [u₂.mem, m₁])
  unfold Hash.padW
  simp only [List.append_assoc]
  have c16 : H.padA + 16 * ((H.P.B - 16 - H.padA) / 16) = H.P.B - 16 := by omega_arith
  refine head _ fun s₁ g₁ x₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine zst_ok H.padA (by omega_arith) ((H.P.B - 16 - H.padA) / 16) _ s₁ Q p (by rw [g₁ _ (by decide) (by decide), hbp])
    x₁ (fun a h1 h2 => by rw [wr₁]; exact hw _ _ (by omega_arith)) (by omega_arith) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The zeros before an 8-byte length field: the block's bytes from `D` to `B - L`.
  have mid : ∀ (rest' : List Instr),
      (∀ t, t.gpr = s₂.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
        t.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.P.B - H.P.L - H.D - 1) 0) →
        WP isa (.block rest') t Q) →
      WP isa (.block ((if H.P.L = 8 then ([.str .x .x10 .x21 (H.P.B - 16)] : List Instr) else []) ++ rest')) s₂ Q := by
    intro rest' k'
    have m₂' : s₂.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D)
        ([0x80] ++ List.replicate (H.P.B - 16 - H.D - 1) 0) := by
      rw [m₂, m₁, Pbkdf2.Memory.writeBytes_append' _ _ _ (by
          rw [List.length_append, List.length_singleton, List.length_replicate, add_ofNat]; congr 2; omega_arith)
          (by simp; omega_arith), List.append_assoc, List.replicate_append_replicate]
      congr 3; omega_arith
    split
    · rename_i h8
      simp only [List.cons_append, List.nil_append]
      refine wp_str (a := p + BitVec.ofNat 64 (H.P.B - 16)) ⟨by omega_arith, by omega_arith⟩
        (by rw [g₂, g₁ _ (by decide) (by decide), hbp]) (by rw [wr₂, wr₁]; exact hw _ _ (by omega_arith)) fun t g => ?_
      refine k' t (by rw [g.gpr]) (by rw [g.rd, rd₂, rd₁]) (by rw [g.wr, wr₂, wr₁]) (by rw [g.sp, sp₂, sp₁]) ?_
      rw [g.mem, g₂, x₁, m₂', writeW_zero8, Pbkdf2.Memory.writeBytes_append' _ _ _ (by
          rw [List.length_append, List.length_singleton, List.length_replicate, add_ofNat]; congr 2; omega_arith)
          (by simp; omega_arith), List.append_assoc, List.replicate_append_replicate]
      congr 3; omega_arith
    · rename_i h8
      exact k' s₂ rfl (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
        (by rw [m₂', show H.P.L = 16 by omega_arith])
  refine mid _ fun t gt rdt wrt spt mt => ?_
  refine wp_movz fun s₃ u₃ => ?_
  change WP isa (.block (H.P.len ++ rest)) s₃ Q
  rw [WP.block_append_iff]
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, gt, g₂, g₁ r h1 h2]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, sp₄, m₄⟩ => ?_
  · rw [g₃ _ (by decide) (by decide) (by decide), hbx, u₃.wr, wrt]; exact hw _ _ (by omega_arith)
  have zx : (BitVec.ofNat 16 (H.P.B + H.D)).setWidth 64 = BitVec.ofNat 64 (H.P.B + H.D) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  rw [g₃ _ (by decide) (by decide) (by decide), hbx, u₃.gpr, zx, M.lenOf_eq _ hok, u₃.mem, mt] at m₄
  have lpz : ([0x80] ++ List.replicate (H.P.B - H.P.L - H.D - 1) 0 : List Byte).length = H.P.B - H.P.L - H.D := by
    simp; omega_arith
  have S1 : Mem.Sep p H.D (p + BitVec.ofNat 64 H.D) (H.P.B - H.P.L - H.D) := by
    have := Offset.sep p (d := 0) (n := H.D) (e := H.D) (k := H.P.B - H.P.L - H.D) (.inl (Nat.le_of_eq (Nat.zero_add _)))
      (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ H.P.B - H.P.L →
      Mem.Sep (p + BitVec.ofNat 64 a) n (p + BitVec.ofNat 64 (H.P.B - H.P.L)) H.P.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_arith) (by omega_arith)
  refine k s₄ (fun r h1 h2 h3 h4 => by rw [g₄ r h1 h3, g₃ r h1 h2 h4]) (by rw [rd₄, u₃.rd, rdt])
    (by rw [wr₄, u₃.wr, wrt]) (by rw [sp₄, u₃.sp, spt]) ?_ ?_ ?_
  · rw [m₄]
    refine (writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)
    · rw [lpz]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [M.lenBytes_length]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · rw [show H.P.B - H.D = (H.P.B - H.P.L - H.D) + H.P.L by omega_arith, bytesAt_add, add_ofNat p,
      show H.D + (H.P.B - H.P.L - H.D) = H.P.B - H.P.L by omega_arith, m₄,
      bytesAt_writeBytes_self' (M.lenBytes_length _) (by omega_arith),
      bytesAt_writeBytes_sep _ _ (by rw [M.lenBytes_length]; exact S2 (by omega_arith)) (by omega_arith),
      bytesAt_writeBytes_self' lpz (by omega_arith), Md.tailPad,
      show H.P.B - H.P.L - 1 - H.D = H.P.B - H.P.L - H.D - 1 by omega_arith]
  · rw [m₄, bytesAt_writeBytes_sep _ _ (by
        rw [M.lenBytes_length]; have := S2 (a := 0) (n := H.D) (by omega_arith); rwa [BitVec.add_zero] at this) (by omega_arith),
      bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega_arith)]

/-- `padSel`: `padW` or `padLen`, which write the same. -/
theorem padSel_ok {H : Hash} {M : Md H.P.B H.P.N H.P.L} (hs : Shape M) (hok : M.lenOk (H.P.B + H.D))
    (hD4 : H.D % 4 = 0) (hB16 : H.P.B % 16 = 0) (hL : H.P.L = 8 ∨ H.P.L = 16) (hA : H.padA + 16 ≤ H.P.B)
    (hpad : H.D + 4 ≤ H.P.B - H.P.L) (hB : H.P.B ≤ 128) {s : State} {p : Addr} (hbp : s.gpr .x21 = p)
    (hbx : s.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = p + BitVec.ofNat 64 (H.P.B - H.P.L))
    (hw : ∀ a n, a + n ≤ H.P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → Frame [⟨p, H.P.B⟩] s.mem s'.mem →
      bytesAt s'.mem (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = M.tailPad H.D →
      bytesAt s'.mem p H.D = bytesAt s.mem p H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.padSel ++ rest)) s Q := by
  unfold Hash.padSel
  split
  · exact padW_ok hs hok hD4 hB16 hL hA hB hbp hbx hw k
  · exact Pbkdf2.AArch64.padLen_ok hs hok hD4 (by omega_arith) (by omega_arith) hpad hB hbp hbx hw
      fun s' g rd wr sp f t d => k s' (fun r h9 _ h12 h22 => g r h9 h12 h22) rd wr sp f t d

end VG.Proof.Pbkdf2.Md.AArch64
