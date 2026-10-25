module

public import VerifiedGarbage.Impl.Pbkdf2.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import all Init.Data.Nat.Bitwise.Basic

/-!
# PBKDF2-HMAC's iteration on RISC-V: bytes

The byte loops of the iteration (`Impl/Pbkdf2/RISCV64.lean`), each unrolled:
copying `n` bytes between offsets of two registers (`cp_ok`), storing a list
of constant bytes (`bytes_ok`, the padding), and exclusive-or'ing `n` bytes
into others (`xor_ok`, `T ← T ⊕ U`). Each writes what `writeBytes` says, and
only `t1` (and `t2`) of the registers.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_lbu wp_sb wp_xor)
open VG.Impl.Pbkdf2.RISCV64 (It)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open Spec.Sha256 (bytesAt)
open Spec.Pbkdf2 (xorBytes)

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = bytesAt m p n ++ [m (p + BitVec.ofNat 64 n)] := by
  simp [bytesAt, List.range_succ]

theorem add_off (p : Addr) (o k : Nat) : p + BitVec.ofNat 64 (o + k) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- A byte past the `n` written at `q`. -/
theorem writeBytes_past {m : Mem} {q x : Addr} {xs : List Byte} (h : ¬ (x - q).toNat < xs.length) :
    writeBytes m q xs x = m x :=
  VG.Proof.Hmac.Common.writeBytes_other _ _ _ h

theorem past_self (q : Addr) {n : Nat} (hn : n < 2 ^ 64) : ¬ (q + BitVec.ofNat 64 n - q).toNat < n := by
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega

/-! ## Copying -/

/-- `n` bytes copied from `src + o₁` to `dst + o₂`, through `t1`. -/
theorem cp_ok {src dst : Reg} (hs : src ≠ .t1) (hd : dst ≠ .t1) (o₁ o₂ : Nat) :
    ∀ (n : Nat), o₁ + n ≤ 2048 → o₂ + n ≤ 2048 → ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 k) 1) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 k) 1) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) n (s.gpr dst + BitVec.ofNat 64 o₂) n →
    (∀ s', (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) n) → WP isa (.block rest) s' Q) →
    WP isa (.block (It.cp src dst o₁ o₂ n ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ _ rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro h₁ h₂ rest s Q hin hout hsep k
    rw [It.cp, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) (by omega) _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_lbu (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 n) (by omega)
      (by rw [g₁ _ hs, add_off]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_sb (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 n) (by omega)
      (by rw [u₂.other _ hd, g₁ _ hd, add_off]) (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ =>
      k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    have hrd : s₁.mem (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 n) =
        s.mem (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 n) := by
      rw [m₁]
      refine writeBytes_past ?_
      rw [VG.Proof.Hmac.Common.bytesAt_length]
      intro hlt
      refine hsep (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 n) ?_ (by omega)
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega
    rw [u₃.mem, u₂.gpr, u₂.mem, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hrd, m₁,
      bytesAt_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega),
      VG.Proof.Hmac.Common.bytesAt_length]

/-! ## Constant bytes -/

/-- The code storing the bytes `xs` at `o(s3)`, through `t1`. -/
def bytesCode (xs : List Nat) (o : Nat) (n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.li .t1 (xs.getD i 0), .store .b .t1 .s3 (o + i)]

theorem padCode_eq (P : It) : P.padCode = bytesCode P.pad P.D P.pad.length := rfl

theorem setWidth_ofNat8 (v : Nat) : (BitVec.ofNat 64 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The first `n` bytes of `xs` at `s3 + o`. -/
theorem bytes_ok (xs : List Nat) (hx : ∀ i < xs.length, xs.getD i 0 < 2048) (o : Nat) :
    ∀ (n : Nat), n ≤ xs.length → o + n ≤ 2048 → ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions s.wr (s.gpr .s3 + BitVec.ofNat 64 o + BitVec.ofNat 64 k) 1) →
    (∀ s', (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr .s3 + BitVec.ofNat 64 o) ((xs.take n).map (BitVec.ofNat 8)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (bytesCode xs o n ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ _ rest s Q _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro h₁ h₂ rest s Q hout k
    rw [bytesCode, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) (by omega) _ s Q (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_li (hx n (by omega)) fun s₂ u₂ => ?_
    refine wp_sb (a := s.gpr .s3 + BitVec.ofNat 64 o + BitVec.ofNat 64 n) (by omega)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide), add_off]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    have hl : ((xs.take n).map (BitVec.ofNat 8)).length = n := by
      simp only [List.length_map, List.length_take]; omega
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, setWidth_ofNat8, List.take_add_one, List.map_append,
      List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_cons, List.map_nil]
    rw [writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < xs.length by omega)]

/-! ## Exclusive-or -/

/-- `n` bytes at `s3` exclusive-or'ed into those at `s5`, through `t1` and `t2`. -/
def xorCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.load .b .t1 .s5 k, .load .b .t2 .s3 k, .logic .xor .t1 .t1 .t2, .store .b .t1 .s5 k]

theorem xorT_eq (P : It) : P.xorT = xorCode P.D := rfl

theorem xor_setWidth (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi
  simp

theorem xorBytes_snoc (a b : List Byte) (x y : Byte) (h : a.length = b.length) :
    xorBytes (a ++ [x]) (b ++ [y]) = xorBytes a b ++ [x ^^^ y] := by
  simp [xorBytes, List.zipWith_append h]

theorem xor_ok : ∀ (n : Nat), n ≤ 2048 → ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .s3 + BitVec.ofNat 64 k) 1) →
    (∀ k < n, InRegions s.wr (s.gpr .s5 + BitVec.ofNat 64 k) 1) →
    Mem.Sep (s.gpr .s5) n (s.gpr .s3) n →
    (∀ s', (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr .s5)
        (xorBytes (bytesAt s.mem (s.gpr .s5) n) (bytesAt s.mem (s.gpr .s3) n)) → WP isa (.block rest) s' Q) →
    WP isa (.block (xorCode n ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [VG.Proof.Hmac.Common.bytesAt_zero, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro h₁ rest s Q hin hout hsep k
    rw [xorCode, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_lbu (a := s.gpr .s5 + BitVec.ofNat 64 n) (by omega) (by rw [g₁ _ (by decide) (by decide)])
      (by rw [rd₁, wr₁]; exact ⟨_, List.mem_append_right _ (hout n (by omega)).choose_spec.1,
        (hout n (by omega)).choose_spec.2⟩) fun s₂ u₂ => ?_
    refine wp_lbu (a := s.gpr .s3 + BitVec.ofNat 64 n) (by omega)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide)])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hin n (by omega)) fun s₃ u₃ => wp_xor fun s₄ u₄ => ?_
    refine wp_sb (a := s.gpr .s5 + BitVec.ofNat 64 n) (by omega)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide)])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₅ u₅ =>
      k s₅ (fun r h1 h2 => by rw [u₅.gpr, u₄.other r h1, u₃.other r h2, u₂.other r h1, g₁ r h1 h2])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem (s.gpr .s5) n) (bytesAt s.mem (s.gpr .s3) n)).length = n := by
      simp [xorBytes, VG.Proof.Hmac.Common.bytesAt_length]
    have ht : s₁.mem (s.gpr .s5 + BitVec.ofNat 64 n) = s.mem (s.gpr .s5 + BitVec.ofNat 64 n) := by
      rw [m₁]; exact writeBytes_past (by rw [hl]; exact past_self _ (by omega))
    have hb : s₁.mem (s.gpr .s3 + BitVec.ofNat 64 n) = s.mem (s.gpr .s3 + BitVec.ofNat 64 n) := by
      rw [m₁]
      refine writeBytes_past ?_
      rw [hl]
      intro hlt
      refine hsep (s.gpr .s3 + BitVec.ofNat 64 n) (by omega) ?_
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      omega
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, xor_setWidth, ht, hb,
      m₁, bytesAt_succ, bytesAt_succ, xorBytes_snoc _ _ _ _ (by simp [VG.Proof.Hmac.Common.bytesAt_length]),
      writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl]

end VG.Proof.Pbkdf2.RISCV64
