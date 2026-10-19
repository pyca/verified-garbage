module
public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MdStream.X86_64.Common

import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.MdStream.X86_64.OneShot
import VerifiedGarbage.Proof.Hmac.Common
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: words

What `copy32` (`Impl/Pbkdf2/Md/X86_64.lean`) writes: 32-bit words copied from
one region to another; and facts about registers and regions the proofs share.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append write_eq_writeBytes)
open VG.Proof.Hmac.Common (copy_mem bytesAt_add bytesAt_writeBytes_sep bytesAt_zero bytesAt_length)
open Spec.Sha256 (bytesAt)

theorem ea_nat (s : State) (b : Reg) (o : Nat) : s.ea (at_ b o) = s.gpr b + BitVec.ofNat 64 o := by
  rw [ea_at, ofInt_natCast]

/-! ## Copies -/

/-- `copy32 src so dst d n` writes the `4 n` bytes at `src + so` to `dst + d`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block (Hash.copy32 src o₁ dst o₂ n ++ rest)) s Q := by
  exact Pbkdf2.X86_64.copy32_ok hs hd o₁ o₂ n

/-- `c` copies of 16-byte words (`cp128`) write the `16 c` bytes at `src + o₁` to `dst + o₂`. -/
theorem copy128_ok {src dst : Reg} (o₁ o₂ : Nat) (c : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < c, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < c, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (16 * k)) 16) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (16 * c) (s.gpr dst + BitVec.ofNat 64 o₂) (16 * c) →
    16 * c < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (16 * c)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range c).flatMap (Hash.cp128 src dst o₁ o₂) ++ rest)) s Q := by
  induction c with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ c ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.cp128, List.cons_append, List.nil_append]
    refine OneShot.wp_movdquLoad (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (16 * c))
      (by rw [Pbkdf2.X86_64.ea_off, g₁]) (by rw [rd₁, wr₁]; exact hin c (by omega)) ?_
    refine wp_movdquStore (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (16 * c))
      (by rw [Pbkdf2.X86_64.ea_off, RegUpd.gpr_setXmm, g₁]) (by rw [RegUpd.wr_setXmm, wr₁]; exact hout c (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (by rw [g₃, RegUpd.gpr_setXmm, g₁])
        (by rw [rd₃, RegUpd.rd_setXmm, rd₁]) (by rw [wr₃, RegUpd.wr_setXmm, wr₁]) ?_
    rw [m₃, RegUpd.xmm_setXmm_self, RegUpd.mem_setXmm, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ c 16 (by rwa [← Nat.mul_succ]) (by omega)

/-- `copyWide src so dst d n` writes the `n` bytes (a multiple of 4) at `src + so` to `dst + d`. -/
theorem copyWide_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ n : Nat) (hn : n % 4 = 0)
    (rest : List Instr) (s : State) (Q : State → Prop)
    (hin : ∀ a w, 0 < w → a + w ≤ n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 a) w)
    (hout : ∀ a w, 0 < w → a + w ≤ n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 a) w)
    (hsep : Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) n (s.gpr dst + BitVec.ofNat 64 o₂) n)
    (hlt : n < 2 ^ 64)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) n) → WP isa (.block rest) s' Q) :
    WP isa (.block (Hash.copyWide src o₁ dst o₂ n ++ rest)) s Q := by
  unfold Hash.copyWide
  simp only [List.append_assoc]
  refine copy128_ok o₁ o₂ (n / 16) _ s Q (fun j hj => hin _ _ (by omega) (by omega)) (fun j hj => hout _ _ (by omega) (by omega))
    (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  -- The 8 bytes after the 16-byte words, if any.
  have step8 : ∀ (rest' : List Instr) (t : State), t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr →
      t.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (16 * (n / 16))) →
      (∀ t', (∀ r, r ≠ .rax → t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr →
        t'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
          (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (n / 8 * 8)) → WP isa (.block rest') t' Q) →
      WP isa (.block ((if n % 16 ≥ 8 then ([.mov .rax (.mem (at_ src (o₁ + 16 * (n / 16)))),
        .store (at_ dst (o₂ + 16 * (n / 16))) .rax] : List Instr) else []) ++ rest')) t Q := by
    intro rest' t g rd wr m k'
    split
    · rename_i h8
      simp only [List.cons_append, List.nil_append]
      refine wp_movm (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (16 * (n / 16)))
        (by rw [Pbkdf2.X86_64.ea_off, g]) (by rw [rd, wr]; exact hin _ _ (by omega) (by omega)) fun t₁ u₁ => ?_
      refine wp_store (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (16 * (n / 16)))
        (by rw [Pbkdf2.X86_64.ea_off, u₁.other _ hd, g]) (by rw [u₁.wr, wr]; exact hout _ _ (by omega) (by omega))
        fun t₂ g₂ m₂ rd₂ wr₂ => k' t₂ (fun r hr => by rw [g₂, u₁.other r hr, g]) (by rw [rd₂, u₁.rd, rd])
          (by rw [wr₂, u₁.wr, wr]) ?_
      rw [m₂, u₁.gpr, u₁.mem, m, show 16 * (n / 16) = 8 * (2 * (n / 16)) by omega,
        show n / 8 * 8 = 8 * (2 * (n / 16)) + 8 by omega]
      exact copy_mem s.mem _ _ (2 * (n / 16)) 8 (fun x hx hy => hsep x (by omega) (by omega)) (by omega)
    · rename_i h8
      exact k' t (fun r _ => by rw [g]) rd wr (by rw [m, show n / 8 * 8 = 16 * (n / 16) by omega])
  refine step8 _ s₁ g₁ rd₁ wr₁ m₁ fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  split
  · rename_i h4
    obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 4 := ⟨(n - 4) / 4, by omega⟩
    have e8 : (4 * q + 4) / 8 * 8 = 4 * q := by omega
    have e4 : 4 * q + 4 - 4 = 4 * q := by omega
    rw [e4]
    rw [e8] at m₂
    simp only [Impl.Pbkdf2.X86_64.cp32, List.cons_append, Nat.mul_zero, Nat.add_zero]
    refine wp_mov32m (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * q))
      (by rw [Pbkdf2.X86_64.ea_off, g₂ _ hs]) (by rw [rd₂, wr₂]; exact hin _ _ (by omega) (by omega)) fun s₃ u₃ => ?_
    refine wp_store32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * q))
      (by rw [Pbkdf2.X86_64.ea_off, u₃.other _ hd, g₂ _ hd]) (by rw [u₃.wr, wr₂]; exact hout _ _ (by omega) (by omega))
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, g₂ r hr]) (by rw [rd₄, u₃.rd, rd₂])
        (by rw [wr₄, u₃.wr, wr₂]) ?_
    rw [m₄, u₃.gpr, u₃.mem, m₂, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    exact copy_mem s.mem _ _ q 4 hsep hlt
  · rename_i h4
    simp only [List.nil_append]
    exact k s₂ g₂ rd₂ wr₂ (by rw [m₂, show n / 8 * 8 = n by omega])

/-- `copyW wide src so dst d n` writes the `n` bytes (a multiple of 4) at `src + so` to `dst + d`. -/
theorem copyW_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (wide : Bool) (o₁ o₂ n : Nat) (hn : n % 4 = 0)
    (rest : List Instr) (s : State) (Q : State → Prop)
    (hin : ∀ a w, 0 < w → a + w ≤ n → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 a) w)
    (hout : ∀ a w, 0 < w → a + w ≤ n → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 a) w)
    (hsep : Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) n (s.gpr dst + BitVec.ofNat 64 o₂) n)
    (hlt : n < 2 ^ 64)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) n) → WP isa (.block rest) s' Q) :
    WP isa (.block (Hash.copyW wide src o₁ dst o₂ n ++ rest)) s Q := by
  unfold Hash.copyW
  split
  · exact copyWide_ok hs hd o₁ o₂ n hn rest s Q hin hout hsep hlt k
  · refine Pbkdf2.X86_64.copy32_ok hs hd o₁ o₂ (n / 4) rest s Q (fun j hj => hin _ _ (by omega) (by omega))
      (fun j hj => hout _ _ (by omega) (by omega)) (fun x hx hy => hsep x (by omega) (by omega)) (by omega)
      fun s' g rd wr m => k s' g rd wr (by rw [m, show 4 * (n / 4) = n by omega])

/-! ## Registers and regions -/

theorem wp_mov32r {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem zx32 (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem contains_pre {b : Addr} {n k : Nat} (h : n ≤ k) : (⟨b, k⟩ : Region).Contains b n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

end VG.Proof.Pbkdf2.Md.X86_64
