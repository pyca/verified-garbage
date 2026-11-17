module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Common
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
import VerifiedGarbage.Proof.Pbkdf2.Memory

/-! ### `Pbkdf2.Md.AArch64.Wide`, which only this module used -/

section

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
  obtain e1 := copy_mem m A B q 8 (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) (by omega_arith)
  obtain e2 := copy_mem m A B (q + 1) 8 (fun x hx hy => hsep x (by omega_arith) (by omega_arith)) (by omega_arith)
  simp only [Nat.reduceMul] at e1 e2
  rw [show 8 * q + 8 = 8 * (q + 1) by omega_arith] at e1
  rw [show 8 * (q + 1) + 8 = 8 * q + 16 by omega_arith] at e2
  obtain sep : Mem.Sep (A + BitVec.ofNat 64 (8 * (q + 1))) 8 (B + BitVec.ofNat 64 (8 * q)) 8 := by
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
  obtain e3 : (writeBytes m B (bytesAt m A (8 * q))).readW (A + BitVec.ofNat 64 (8 * q) + 8) 64 =
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
    obtain i0 := hin c (by omega_arith) 0 (by omega_arith)
    obtain i1 := hin c (by omega_arith) 1 (by omega_arith)
    obtain o0 := hout c (by omega_arith) 0 (by omega_arith)
    obtain o1 := hout c (by omega_arith) 1 (by omega_arith)
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
    obtain step8 : ∀ (rest' : List Instr) (t : State), (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) →
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
        refine wp_ldr (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (16 * (n / 16))) ⟨by omega, by omega_using [h₁]⟩
          (by rw [g _ hs.1 hs.2, add_ofNat]) (by rw [rd, wr]; exact hin _ _ (by omega_arith) (by omega_arith)) fun t₁ u₁ => ?_
        refine wp_str (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (16 * (n / 16))) ⟨by omega, by omega_using [h₂]⟩
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
      obtain e8 : (4 * q + 4) / 8 * 8 = 4 * q := by omega_arith
      obtain e4 : 4 * q + 4 - 4 = 4 * q := by omega_arith
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
    obtain hl : (List.replicate (16 * c) (0 : Byte)).length + 16 < 2 ^ 64 := by
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
  obtain hAD : H.D + 4 ≤ H.padA := by simp only [Hash.padA]; omega_arith
  obtain hA16 : H.padA % 16 = 0 := by simp only [Hash.padA]; omega_arith
  obtain hAD' : H.padA ≤ H.D + 16 := by simp only [Hash.padA]; omega_arith
  -- The head: `0x80` and zeros from `D` up to `padA`, and zero in `x10`.
  obtain head : ∀ (rest' : List Instr),
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
      obtain e : H.padA - H.D - 1 = 15 := by simp only [Hash.padA]; omega_arith
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
  obtain c16 : H.padA + 16 * ((H.P.B - 16 - H.padA) / 16) = H.P.B - 16 := by omega_arith
  refine head _ fun s₁ g₁ x₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine zst_ok H.padA (by omega_arith) ((H.P.B - 16 - H.padA) / 16) _ s₁ Q p (by rw [g₁ _ (by decide) (by decide), hbp])
    x₁ (fun a h1 h2 => by rw [wr₁]; exact hw _ _ (by omega_arith)) (by omega_arith) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The zeros before an 8-byte length field: the block's bytes from `D` to `B - L`.
  obtain mid : ∀ (rest' : List Instr),
      (∀ t, t.gpr = s₂.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
        t.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.P.B - H.P.L - H.D - 1) 0) →
        WP isa (.block rest') t Q) →
      WP isa (.block ((if H.P.L = 8 then ([.str .x .x10 .x21 (H.P.B - 16)] : List Instr) else []) ++ rest')) s₂ Q := by
    intro rest' k'
    obtain m₂' : s₂.mem = writeBytes s.mem (p + BitVec.ofNat 64 H.D)
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
  obtain g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x22 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, gt, g₂, g₁ r h1 h2]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, sp₄, m₄⟩ => ?_
  · rw [g₃ _ (by decide) (by decide) (by decide), hbx, u₃.wr, wrt]; exact hw _ _ (by omega_arith)
  obtain zx : (BitVec.ofNat 16 (H.P.B + H.D)).setWidth 64 = BitVec.ofNat 64 (H.P.B + H.D) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  rw [g₃ _ (by decide) (by decide) (by decide), hbx, u₃.gpr, zx, M.lenOf_eq _ hok, u₃.mem, mt] at m₄
  obtain lpz : ([0x80] ++ List.replicate (H.P.B - H.P.L - H.D - 1) 0 : List Byte).length = H.P.B - H.P.L - H.D := by
    simp; omega_arith
  obtain S1 : Mem.Sep p H.D (p + BitVec.ofNat 64 H.D) (H.P.B - H.P.L - H.D) := by
    have := Offset.sep p (d := 0) (n := H.D) (e := H.D) (k := H.P.B - H.P.L - H.D) (.inl (Nat.le_of_eq (Nat.zero_add _)))
      (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  obtain S2 : ∀ {a n : Nat}, a + n ≤ H.P.B - H.P.L →
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

end

end

/-! ### `Pbkdf2.Md.AArch64.HmacFinInner`, which only this module used -/

section

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize` up to the inner digest

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacFinInner.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) starts by saving our caller's registers and
our return address (`pro_ok`) and finalizing the inner state into `scratch`
with the streaming `finalize` (`fin1Args_ok`, `finCall_ok`): what holds from
the prologue on (`KR`), and that call in two runs (`fin_rel'`). The rest is
`Proof/Pbkdf2/Md/AArch64/HmacFin.lean`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Impl.MdStream.AArch64 (mov)
open VG.Proof.Pbkdf2.Md.AArch64.Calls
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub off_disj off_disj0 covers_one sub_of_off sub_of_self)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt sub_offset contains_offset Upd wp_mov wp_movz wp_addImm)
open Spec.Sha256 (bytesAt)

variable {H : Stream} (hH : StreamOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev outer : Addr := s₀.gpr .x1
abbrev op : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outerR : Region := ⟨outer s₀, H.S⟩
abbrev opR : Region := ⟨op s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev stkR : Region := below s₀.sp 16
/-- Where the digests go. -/
abbrev T : Addr := scr s₀ + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outerR (H := H) s₀]
  wr : s₀.wr = [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outerR (H := H) s₀)
  i_p : (inR (H := H) s₀).Disjoint (opR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_p : (outerR (H := H) s₀).Disjoint (opR (H := H) s₀)
  o_s : (outerR (H := H) s₀).Disjoint (scR sc s₀)
  p_s : (opR (H := H) s₀).Disjoint (scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  stk_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 134
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (tR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Stream.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 56) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 56) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 56) (b := 8 * H.W + 56) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x20 : s.gpr .x20 = outer s₀
  x21 : s.gpr .x21 = op s₀
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x21, .x23, .x25, .x26, .x27, .x28]

theorem untouched_kregs : ∀ r ∈ untouched, r ∈ kregs := by decide
theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (untouched_kregs r hr)).trans (h.cs r hr), h.saved.frame H hf hs⟩

theorem KR.regs {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s s' d v) : KR (H := H) s₀ s' :=
  h.regs u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

theorem KR.call {s₀ s s' : State} (h : KR (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws ++ [stkR s₀], (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [h.sp] at f
  exact h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f hs

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) s₀ s ∧ s.gpr .x0 = inn s₀ ∧
    s.gpr .x2 = s₀.gpr .x2 ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Stream.buf] at this; omega_nat
  refine save_ok H (scr := scr s₀) rfl (Nat.le_trans hp.hW (by decide)) (wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    fun r hr => k r (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide)
      (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide),
    hm ▸ sv₁⟩, k _ (by decide) (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide) (by decide), hm ▸ f₁⟩

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) s₀ t) (h0 : t.gpr .x0 = inn s₀)
    (h2 : t.gpr .x2 = T (H := H) s₀) (h3 : t.gpr .x3 = scr s₀) :
    FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) := by
  have hwb := hH.hWb; have hf := hp.fits; simp only [Stream.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { x0 := h0, x2 := h2, x3 := h3
      cw := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := (cal_t hH hp).symm
      sp16 := by rw [hk.sp]; exact hp.sp16
      stk_st := by rw [hk.sp]; exact hp.stk_i
      stk_o := by rw [hk.sp]; exact hp.stk_s.sub_right (t_sub hp)
      stk_sc := by rw [hk.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem buf_lt : H.buf < 4096 := by
  have := hp.hW; simp only [Stream.buf]; omega_nat

/-- The first call's arguments: the count from `x2`. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) s₀ s) (h0 : s.gpr .x0 = inn s₀) {c : BitVec 64}
    (h2 : s.gpr .x2 = c) :
    WP isa (.block ([] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr))) s fun t =>
      KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addImm (buf_lt hp) fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  have k₃ : KR (H := H) s₀ s₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine ⟨k₃, finArgs hH hp k₃ ?_ ?_ ?_, ?_, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hk.x23]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2]

theorem finCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', VecKept t s' → KR (H := H) s₀ s' → Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (inn s₀) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.sp] at f
    refine hQ s' ha'.vec (hk.call ha' ?_) f hpost
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_s.symm.sub_left (save_sub hp)
    · exact save_t hp
    · exact (cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (save_sub hp)

end

/-! ## In two runs -/

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x23]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Stream) : List Instr :=
  [] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr)

variable {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, inn, inn, hq.x0]
  · rw [h.x20, h'.x20, outer, outer, hq.x1]
  · rw [h.x21, h'.x21, op, op, hq.x3]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.x0.symm, by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm⟩

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .x1 = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .x1 = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c)
    pubRegs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ _ k' _ _ => k'))

end VG.Proof.Pbkdf2.Md.AArch64.HmacFin

end

end

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize`

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) starts by finalizing the inner state into
`scratch` (`Proof/Pbkdf2/Md/AArch64/HmacFin.lean`); then it computes the outer hash with one compression, as `iterate`
does (`Proof/Pbkdf2/AArch64/Iterate.lean`): it writes the outer hash value
over the inner state's and, into its buffer, the inner digest and the padding
(`finMid`, `mid_ok`), compresses that block (`cmp_ok`) and writes the digest
of the result to `out` (`finOut`, `out_ok`). That this is the outer hash is
`Md.Link.hash_block`. Everything up to the inner digest is
`HmacFinInner.lean`'s, for the hash function's streaming functions
(`HashOK.stream`);
constant time likewise, from the taint checks of the pieces between the calls
(`Checks`) and the compression function's own proof (`compressAt_rel`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream.AArch64 (add_ofNat wp_mov wp_addImm)
open VG.Impl.MdStream.AArch64 (compressAt compressWith mov)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (CallOk compressAt_ok compressAt_rel)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (finG FinArgs rel_taint rel_wp fin_rel restore_ok saveR SavedRegs VecKept
  savedRegs repr_keep PubEq args untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The registers the code after the inner digest keeps public: `inner`, the
block (its buffer), `scratch` and `out`. -/
abbrev oregs : List Reg := [.x19, .x21, .x23, .x24]

/-- The registers `KO` fixes. -/
abbrev koregs : List Reg := [.x19, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs oregs) (.block H.finOut) hc).isSome = true

/-- The block: the inner state's buffer. -/
abbrev blk (H : Hash) (s₀ : State) : Addr := inn s₀ + BitVec.ofNat 64 H.P.N

/-- What holds from the outer block on: as `KR`, but `outer` is no longer
needed, and `out` is in `x24`. -/
structure KO (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x23 : s.gpr .x23 = scr s₀
  x24 : s.gpr .x24 = op s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem

theorem untouched_ko : ∀ r ∈ untouched, r ∈ koregs := by decide

theorem KO.keep {s₀ s s' : State} (h : KO H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ koregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.stream (scr s₀)).Disjoint r) : KO H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19, (hg _ (by simp)).trans h.x23,
    (hg _ (by simp)).trans h.x24, fun r hr => (hg r (untouched_ko r hr)).trans (h.cs r hr),
    h.saved.frame H.stream hf hs⟩

omit hH in
/-- The end: `abiPreserved`, from `KO` and `restore`. -/
theorem abi_of {s₀ s s' : State} (hk : KO H s₀ s) (hsp : s'.sp = s.sp) (hv : VecKept s₀ s')
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) (ho : ∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, by rw [hsp, hk.sp], hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hg _ (by decide)
    | exact (ho _ (by decide)).trans (hk.cs _ (by decide))

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.P.L % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.D + 4 ≤ H.P.B - H.P.L ∧
    0 < H.D ∧ H.D ≤ H.P.N ∧ H.P.N + H.P.L ≤ H.P.B ∧ H.P.B ≤ 128 ∧ H.P.so % 8 = 0 ∧
    H.P.so + 104 + H.P.N ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 ∧ H.P.so + 104 + H.P.N ≤ 4096 := by
  have := hH.sizes.N4; have := hH.sizes.D4; have := hH.sizes.L4; have := hH.sizes.pad; have := hH.sizes.D0
  have := hH.sizes.DN; have := hH.sizes.NL; have hH_B_le := hH.B_le; have := hH.sizes.dims.so; have hH_N_le := hH.N_le
  obtain hp_nw := hp.nw; have hp_hS := hp.hS
  have : H.P.md.so = H.P.so := rfl
  have : H.P.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega_using [h]
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hb : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 56 := rfl
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  omega_arith

omit hH hp in
/-- The ranges of the inner state, which holds the hash value and the block. -/
theorem in_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    Region.Sub ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ (inR (H := H.stream) s₀) :=
  Offset.sub_base _ h

omit hH in
theorem save_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (saveR H.stream (scr s₀)).Disjoint ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (save_sub hp)).sub_right (in_inR h)

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it; `x20` = `scratch`, `x24` = `out`, and the
block's address in `x21` and `x1`. -/
theorem mid_ok {s : State} (hk : KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => KO H s₀ t ∧ t.gpr .x20 = scr s₀ ∧ t.gpr .x21 = blk H s₀ ∧
      t.gpr .x1 = blk H s₀ ∧
      (∀ i < H.P.N, t.mem (inn s₀ + BitVec.ofNat 64 i) = s.mem (outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (blk H s₀) H.D = bytesAt s.mem (T (H := H.stream) s₀) H.D ∧
      bytesAt t.mem (blk H s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.md.tailPad H.D := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, -, h8, hSB, h4k⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain hbuf : H.stream.buf % 4 = 0 ∧ H.stream.buf + H.P.N ≤ 8 * sc ∧ H.stream.buf + H.P.N ≤ 4096 := by
    have : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 56 := rfl
    have : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
    omega_arith
  clear h4k
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  obtain oR : outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  obtain tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (scR sc s₀) := Offset.sub_base _ (by omega_using [hbuf, hDN])
  simp only [Hash.finMid, List.append_assoc]
  refine copyW_ok (src := .x20) (dst := .x19) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ _ 0 0 H.P.N hN4
    ⟨rfl, by omega_using [hB, hNL]⟩ ⟨rfl, by omega_using [hbuf]⟩ _ s _
    (fun a w hw ha => by
      rw [hk.x20, add_ofNat]
      exact ⟨_, oR, Offset.contains_base _ (by omega_using [ha, hS]) (by omega_using [ha, hB, hNL])⟩)
    (fun a w hw ha => by
      rw [hk.x19, add_ofNat, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [hS, ha]) (by omega_using [hbuf, ha])⟩)
    (by
      rw [hk.x20, hk.x19]
      exact hp.i_o.symm.sep (Offset.contains_base _ (by omega_using [hS]) (Nat.two_pow_pos 64))
        (Offset.contains_base _ (by omega_using [hS]) (Nat.two_pow_pos 64)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [hk.x20, hk.x19, z, z] at m₁
  obtain x23 : s₁.gpr .x23 = scr s₀ := by rw [g₁ _ (by decide) (by decide), hk.x23]
  obtain x19 : s₁.gpr .x19 = inn s₀ := by rw [g₁ _ (by decide) (by decide), hk.x19]
  refine copyW_ok (src := .x23) (dst := .x19) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ _ H.stream.buf H.P.N H.D
    hD4 ⟨by omega_using [hbuf], by omega_using [hbuf, hDN]⟩ ⟨hN4, by omega_using [hB, hNL, hpad]⟩ _ s₁ _
    (fun a w hw ha => by
      rw [x23, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega_using [ha, hbuf, hDN]) (by omega_using [ha, hbuf, hDN])⟩)
    (fun a w hw ha => by
      rw [x19, add_ofNat, wr₁, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [ha, hS, hpad]) (by omega_using [ha, hB, hNL, hpad])⟩)
    (by
      rw [x23, x19]
      exact hp.i_s.symm.sep (Offset.contains_base _ (by omega_using [hDN, hbuf]) (by omega_using [hbuf]))
        (Offset.contains_base _ (by omega_using [hS, hpad]) (hH.sizes.N_lt64)))
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  rw [x23, x19] at m₂
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => wp_addImm (hH.N_lt4096) fun s₄ u₄ => wp_mov fun s₅ u₅ => ?_
  obtain x21₅ : s₅.gpr .x21 = blk H s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide) (by decide), x19]
  obtain G₅ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x20 → r ≠ .x21 → r ≠ .x24 → s₅.gpr r = s₁.gpr r :=
    fun r h1 h0 h2 h3 h4 => by rw [u₅.other r h2, u₄.other r h3, u₃.other r h4, g₂ r h1 h0]
  obtain hB16 : H.P.B % 16 = 0 := by rcases hH.sizes.B with h | h <;> rw [h]
  refine padSel_ok hH.shape (hH.lenOk _ (by omega_using [hB, hpad])) hD4 hB16 hH.L816 hH.hPad hpad hB (s := s₅) x21₅
    (by rw [G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), x19, add_ofNat,
      show H.P.N + (H.P.B - H.P.L) = H.P.N + H.P.B - H.P.L by omega_using [hpad]])
    (fun a n h' => by
      rw [u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr, add_ofNat]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [h', hS]) (by omega_using [h', hB, hNL])⟩) fun s₆ g₆ rd₆ wr₆ sp₆ f₆ p₆ d₆ => ?_
  refine wp_mov fun s₇ u₇ => WP.block_nil ?_
  obtain G : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x1 → s₇.gpr r = s₅.gpr r :=
    fun r h1 h0 h2 h3 h4 => by rw [u₇.other r h4, g₆ r h1 h0 h2 h3]
  have hm : s₇.mem = s₆.mem := u₇.mem
  obtain f₁ : Frame [⟨inn s₀, H.P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain f₂ : Frame [⟨blk H s₀, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain f₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  rw [f₅] at f₆ d₆
  obtain fI : Frame [inR (H := H.stream) s₀] s.mem s₇.mem := by
    rw [hm]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₆.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hS])⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (Nat.add_le_add_left hH.sizes.D_le_B _)⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (Nat.le_refl _)⟩
  obtain Gk : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x1 → r ≠ .x20 → r ≠ .x21 → r ≠ .x24 →
      s₇.gpr r = s.gpr r := fun r h1 h0 h2 h3 h4 h5 h6 h7 => by
    rw [G r h1 h0 h2 h3 h4, G₅ r h1 h0 h5 h6 h7, g₁ r h1 h0]
  obtain hu : ∀ r ∈ untouched, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x22 ∧ r ≠ .x1 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧
      r ≠ .x24 := by
    decide
  refine ⟨⟨by rw [u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁, hk.rd],
      by rw [u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr],
      by rw [u₇.sp, sp₆, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁, hk.sp],
      by rw [Gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk.x19],
      by rw [Gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk.x23],
      by rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hk.x21],
      fun r hr => by
        obtain ⟨h1, h0, h2, h3, h4, h5, h6, h7⟩ := hu r hr
        rw [Gk r h1 h0 h2 h3 h4 h5 h6 h7, hk.cs r hr],
      hk.saved.frame H.stream fI (by
        simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp))⟩,
    by rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hk.x23],
    by rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), x21₅],
    by rw [u₇.gpr, g₆ _ (by decide) (by decide) (by decide) (by decide), x21₅], fun i hi => ?_, ?_, by rw [hm]; exact p₆⟩
  · -- The hash value: the outer one, which the later pieces keep.
    obtain hd : ∀ {a n : Nat}, H.P.N ≤ a → a + n ≤ H.P.N + H.P.B →
        ∀ r ∈ [(⟨inn s₀ + BitVec.ofNat 64 a, n⟩ : Region)], Region.Disjoint ⟨inn s₀, H.P.N⟩ r := fun ha hn => by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ ha (by omega_using [hn, hB, hNL])
    rw [hm, f₆.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (Nat.le_refl _)) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      f₂.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (Nat.add_le_add_left hH.sizes.D_le_B _)) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hB, hNL]),
      bytesAt_getD' _ _ hi]
  · -- The inner digest.
    rw [hm, d₆, m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hH.sizes.D_lt64)]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm.sub_right (Region.sub_prefix (by omega_using [hS]))) (hH.sizes.D_le64)

/-- What the call of the compression function needs. -/
theorem callOk {t : State} (hk : KO H s₀ t) (h20 : t.gpr .x20 = scr s₀) (h1 : t.gpr .x1 = blk H s₀) :
    CallOk t H.P.N H.P.B H.P.so (inn s₀) (scr s₀) (blk H s₀) := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  obtain z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  obtain hv : Region.Sub ⟨inn s₀, H.P.N⟩ (inR (H := H.stream) s₀) := Region.sub_prefix (by omega_using [hS])
  obtain hb : Region.Sub ⟨blk H s₀, H.P.B⟩ (inR (H := H.stream) s₀) := in_inR (Nat.le_refl _)
  obtain hs : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := Region.sub_prefix (by omega_using [hf])
  refine ⟨hk.x19, h20, h1, (hp.i_s.sub_left hv).sub_right hs, Offset.disjoint_base _ (Nat.le_refl _) (hH.NB_le64),
    (hp.i_s.sub_left hb).sub_right hs, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ iR, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hf]⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hf]⟩

/-- The compression of the block into the hash value. -/
theorem cmp_ok {t : State} (hk : KO H s₀ t) (h20 : t.gpr .x20 = scr s₀) (h1 : t.gpr .x1 = blk H s₀)
    {Q : State → Prop}
    (k : ∀ s', KO H s₀ s' → s'.gpr .x21 = t.gpr .x21 →
      hH.md.stateAt s'.mem (inn s₀) = hH.md.compress (hH.md.stateAt t.mem (inn s₀))
        (hH.md.blockAt t.mem (blk H s₀)) → Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  obtain z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  obtain kp : ∀ r ∈ koregs, r ∈ preserved ∧ r ≠ .x30 := by decide
  refine compressAt_ok hH.comp (callOk hH hp hk h20 h1) fun s' hrd hwr hcs hsp hfr hst =>
    k s' (hk.keep hrd hwr hsp (fun r hr => hcs r (kp r hr).1 (kp r hr).2) hfr ?_)
      (hcs _ (by decide) (by decide)) hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · have := save_inR hp (a := 0) (n := H.P.N) (Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) (Nat.le_add_right _ _)); rwa [z] at this
  · exact (Offset.base_disjoint (scr s₀) (k := H.P.so) (e := 8 * H.stream.W) (n := 56)
      (by show H.P.so ≤ 8 * ((H.P.so + 48) / 8); omega_using [])
      (by show 8 * ((H.P.so + 48) / 8) + 56 ≤ 2 ^ 64; omega_using [h8, hf])).symm

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KO H s₀ s) (h21 : s.gpr .x21 = blk H s₀) :
    WP isa (.block H.finOut) s fun s' => ∃ t, KO H s₀ t ∧
      bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
      s'.sp = t.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  obtain hdl := hH.md.digest_length (hH.md.stateAt s.mem (inn s₀))
  obtain k9 : ∀ r ∈ koregs, r ≠ .x9 := by decide
  obtain k10 : ∀ r ∈ koregs, r ≠ .x10 := by decide
  obtain hL : 8 * H.stream.W + 56 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 56 := rfl
    have hp_fits := hp.fits
    omega_using [hp_fits, this]
  obtain fin : ∀ t, KO H s₀ t → bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D →
      WP isa (.block H.stream.restore) t fun s' => ∃ t, KO H s₀ t ∧
        bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
        s'.sp = t.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → s'.gpr r = t.gpr r) :=
    fun t kt bt =>
      WP.mono (restore_ok H.stream kt.x23 (Nat.le_trans hp.hW (by decide)) kt.saved (by rw [kt.wr]; exact sR) hL)
        fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨t, kt, bt, hm, hsp, hg, ho⟩
  obtain x19_in : InRegions (s.rd ++ s.wr) (s.gpr .x19) H.P.N := by
    have := Offset.contains_base (inn s₀) (d := 0) (n := H.P.N) (k := H.P.N + H.P.B) (Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) (Nat.le_add_right _ _)) (Nat.two_pow_pos 64)
    rw [z] at this
    rw [hk.x19, hk.rd, hk.wr]
    exact ⟨_, List.mem_append_right _ iR, this⟩
  unfold Hash.finOut
  by_cases hDN' : H.D < H.P.N
  · simp only [hDN', ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (hH.shape.out s x19_in (by
        rw [h21, hk.wr]; exact ⟨_, iR, Offset.contains_base _ (by omega_using [hS, hNL]) (hH.sizes.N_lt64)⟩)
      (by rw [hk.x19, h21]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hNL])))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
    rw [h21, hk.x19] at m₁
    obtain f₁ : Frame [⟨blk H s₀, H.P.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    obtain k₁ : KO H s₀ s₁ := hk.keep rd₁ wr₁ sp₁ (fun r hr => g₁ r (k9 r hr)) f₁
      (by simp only [List.mem_singleton]; rintro r rfl; exact save_inR hp (by omega_using [hNL]))
    obtain b₁ : bytesAt s₁.mem (blk H s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D := by
      rw [bytesAt_take _ _ (Nat.le_of_lt hDN'), m₁, bytesAt_writeBytes_self' hdl (hH.sizes.N_lt64)]
    obtain x21₁ : s₁.gpr .x21 = blk H s₀ := by rw [g₁ _ (by decide), h21]
    refine copyW_ok (src := .x21) (dst := .x24) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ _ 0 0 H.D hD4
      ⟨rfl, by omega_using [hB, hpad]⟩ ⟨rfl, by omega_using [h4k, hDN']⟩ _ s₁ _
      (fun a w hw ha => by
        rw [x21₁, add_ofNat, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
        exact ⟨_, List.mem_append_right _ iR, Offset.contains_base _ (by omega_using [ha, hS, hpad]) (by omega_using [h4k, hDN', ha])⟩)
      (fun a w hw ha => by
        rw [k₁.x24, add_ofNat, k₁.wr]
        exact ⟨_, pR, Offset.contains_base _ (by show 0 + a + w ≤ H.D; omega_using [ha]) (by omega_using [ha, hB, hpad])⟩)
      (by
        rw [x21₁, k₁.x24, add_ofNat]
        exact hp.i_p.sep (Offset.contains_base _ (by omega_using [hS, hpad]) (by omega_using [hB, hNL]))
          (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega_using []) (Nat.two_pow_pos 64)))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
    rw [x21₁, k₁.x24, z, z] at m₂
    refine fin s₂ (k₁.keep rd₂ wr₂ sp₂ (fun r hr => g₂ r (k9 r hr) (k10 r hr))
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [bytesAt_length]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hH.sizes.D_lt64), b₁]
  · have eDN : H.D = H.P.N := by omega_using [hDN', hDN]
    simp only [hDN', ↓reduceIte, List.cons_append]
    refine wp_mov fun s₁ u₁ => ?_
    rw [WP.block_append_iff]
    obtain x19₁ : s₁.gpr .x19 = inn s₀ := by rw [u₁.other _ (by decide), hk.x19]
    refine WP.mono (hH.shape.out s₁ (by rw [u₁.rd, u₁.wr, u₁.other _ (by decide)]; exact x19_in) (by
        rw [u₁.gpr, hk.x24, u₁.wr, hk.wr, ← eDN]; exact ⟨_, pR, Region.contains_self _ _⟩)
      (by rw [x19₁, u₁.gpr, hk.x24, ← eDN]; exact hp.i_p.sub_left (Region.sub_prefix (by omega_using [hS, hpad]))))
      fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
    rw [x19₁, u₁.gpr, hk.x24, u₁.mem] at m₂
    refine fin s₂ (hk.keep (rd₂.trans u₁.rd) (wr₂.trans u₁.wr) (sp₂.trans u₁.sp) (fun r hr => by
        rw [g₂ r (k9 r hr), u₁.other r (by revert hr; revert r; decide)])
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [hdl, ← eDN]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (hH.sizes.N_lt64), List.take_of_length_le (by omega_using [hdl])]

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (WP.preservedV (pro_ok hp) (by rfl)) fun s₁ ⟨⟨k₁, di₁, dx₁, f₁⟩, hv₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (WP.preservedV (fin1Args_ok hH.stream hp k₁ di₁ dx₁) (by rfl))
    fun t₁ ⟨⟨kt₁, a₁, si₁, m₁⟩, hva₁⟩ => finCall_ok hH.stream hp kt₁ a₁ fun s₂ hv₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (WP.preservedV (mid_ok hH hp k₂) (by rw [Code.allInstrs_eq]; exact hH.finMid_keepsV))
    fun s₃ ⟨⟨k₃, x20₃, x21₃, x1₃, i₃, b₃, p₃⟩, hv₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (cmp_ok hH hp k₃ x20₃ x1₃ (Q := fun s' => KO H s₀ s' ∧
      s'.gpr .x21 = s₃.gpr .x21 ∧ hH.md.stateAt s'.mem (inn s₀) =
        hH.md.compress (hH.md.stateAt s₃.mem (inn s₀)) (hH.md.blockAt s₃.mem (blk H s₀)))
      fun s₄ k₄ x21₄ e₄ => ⟨k₄, x21₄, e₄⟩)
    (by rw [Code.allInstrs_eq]; exact hH.cmp_keepsV)) fun s₄ ⟨⟨k₄, x21₄, e₄⟩, hv₄⟩ => ?_)
  refine WP.mono (WP.preservedV (out_ok hH hp k₄ (x21₄.trans x21₃))
    (by rw [Code.allInstrs_eq]; exact hH.finOut_keepsV))
    fun s' ⟨⟨s₅, k₅, m₅, hm, hsp, hg, ho⟩, hv₅⟩ => ⟨abi_of k₅ hsp (fun r hr => by
      rw [hv₅ r hr, hv₄ r hr, hv₃ r hr, hv₂ r hr, hva₁ r hr, hv₁ r hr]) hg ho, ?_⟩
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hH.hB] at hk0 hcnt
  obtain hl0 : (xorPad k0 ipad ++ text).length = H.P.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until the inner digest is written.
  obtain oI : ∀ r ∈ [saveR H.stream (scr s₀)], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (save_sub hp)
  obtain o₂ : ∀ r ∈ [inR (H := H.stream) s₀, tR (H := H.stream) s₀, calR hH.stream s₀,
      stkR s₀], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (cal_sub hH.stream hp)
    · exact hp.stk_o.symm
  obtain rO₂ := repr_keep hH.stream f₂ o₂ (m₁ ▸ repr_keep hH.stream f₁ oI hrO)
  -- The inner digest.
  obtain dig : (bytesAt s₂.mem (T (H := H.stream) s₀) H.P.N).take H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) :=
    d₂ _ (m₁ ▸ repr_keep hH.stream f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The outer hash: one compression of the outer hash value.
  obtain hxl : (xorPad k0 opad).length = H.P.B := by rw [xorPad_length, hk0]
  obtain ho : hH.md.stateAt s₃.mem (inn s₀) = hH.md.compressList hH.iv (xorPad k0 opad) 1 := by
    rw [hH.reloc s₂.mem s₃.mem (outer s₀) (inn s₀) i₃]
    exact Md.stateAt_of_repr hB0 hxl ((hH.repr _ _ _).1 rO₂)
  show bytesAt s'.mem (op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hm, m₅, e₄, ho, hH.md.blockAt_eq (hH.sizes.D_le_B) p₃, b₃, hmacBlockKey, ← dig,
    ← bytesAt_take _ _ hDN, hH.iterOk.link.hash_block hxl (bytesAt_length _ _ _)]

end

/-! ## Constant time -/

section

variable {sc : Nat} {s₀ s₀' : State} (hp : Pre (H := H.stream) sc s₀) (hp' : Pre (H := H.stream) sc s₀')
  (hq : PubEq s₀ s₀')

omit hH in
/-- The registers `oregs` and the stack pointer agree in two runs. -/
theorem ko_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KO H s₀ s ∧ s.gpr .x21 = blk H s₀)
    (h' : KO H s₀' s' ∧ s'.gpr .x21 = blk H s₀') : s.sp = s'.sp ∧ ∀ r ∈ oregs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.1.sp, h'.1.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.1.x19, h'.1.x19, inn, inn, hq.x0]
  · rw [h.2, h'.2, blk, blk, inn, inn, hq.x0]
  · rw [h.1.x23, h'.1.x23, scr, scr, hq.x4]
  · rw [h.1.x24, h'.1.x24, op, op, hq.x3]

omit hH in
theorem callOk_congr {t : State} {N B so : Nat} {a b c a' b' c' : Addr} (h : CallOk t N B so a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : CallOk t N B so a' b' c' := by
  subst ha hb hc; exact h

include hH hp hp' hq

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.stream.finPrologue)
      fun s s' => (KR (H := H.stream) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2) ∧
        (KR (H := H.stream) s₀' s' ∧ s'.gpr .x0 = inn s₀' ∧ s'.gpr .x2 = s₀'.gpr .x2) :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  obtain fin1 := fin_rel' hH.stream hp hp' hq (c := s₀.gpr .x2)
    (F := fun s => KR (H := H.stream) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2)
    (F' := fun s => KR (H := H.stream) s₀' s ∧ s.gpr .x0 = inn s₀' ∧ s.gpr .x2 = s₀'.gpr .x2) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH.stream hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH.stream hp' k d x) fun _ ⟨k, a, si, m⟩ =>
      ⟨k, a, si.trans hq.x2.symm, m⟩)
  obtain mid : RelCT isa (fun s s' => KR (H := H.stream) s₀ s ∧ KR (H := H.stream) s₀' s') (.block H.finMid)
      fun s s' => (KO H s₀ s ∧ s.gpr .x20 = scr s₀ ∧ s.gpr .x21 = blk H s₀ ∧ s.gpr .x1 = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .x20 = scr s₀' ∧ s'.gpr .x21 = blk H s₀' ∧ s'.gpr .x1 = blk H s₀') :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hc.mid
      (fun s k => WP.mono (mid_ok hH hp k) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
      (fun s k => WP.mono (mid_ok hH hp' k) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  have e₀ : inn s₀' = inn s₀ := hq.x0.symm
  have e₄ : scr s₀' = scr s₀ := hq.x4.symm
  obtain eb : blk H s₀' = blk H s₀ := by rw [blk, blk, e₀]
  obtain cmp : RelCT isa (fun s s' =>
        (KO H s₀ s ∧ s.gpr .x20 = scr s₀ ∧ s.gpr .x21 = blk H s₀ ∧ s.gpr .x1 = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .x20 = scr s₀' ∧ s'.gpr .x21 = blk H s₀' ∧ s'.gpr .x1 = blk H s₀'))
      (compressAt H.compN H.compC)
      fun s s' => (KO H s₀ s ∧ s.gpr .x21 = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .x21 = blk H s₀') :=
    rel_wp (compressAt_rel hH.comp fun s s' ⟨⟨k, x20, _, x1⟩, ⟨k', x20', _, x1'⟩⟩ =>
        ⟨callOk hH hp k x20 x1, callOk_congr (callOk hH hp' k' x20' x1') e₀ e₄ eb, by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun s ⟨k, x20, x21, x1⟩ => cmp_ok hH hp k x20 x1 fun s' k' e _ => ⟨k', e.trans x21⟩)
      (fun s ⟨k, x20, x21, x1⟩ => cmp_ok hH hp' k x20 x1 fun s' k' e _ => ⟨k', e.trans x21⟩)
  obtain ⟨_, hr⟩ := hc.out
  obtain out : RelCT isa (fun s s' => (KO H s₀ s ∧ s.gpr .x21 = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .x21 = blk H s₀'))
      (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs oregs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := ko_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (fin1.seq (mid.seq (cmp.seq out)))

end

/-- HMAC's `finalize` is verified against `finG`, given the taint checks. -/
theorem verified {sc : Nat} (hc : Checks H) (hfit : H.stream.buf + H.stream.F ≤ 8 * sc)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified AArch64.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH.stream sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH.stream sc h₁ hfit) (pre_of hH.stream sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.HmacFin
