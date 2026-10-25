module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

import Mathlib.Data.List.Induction
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State

/-! # Wrapped addition across an entire seed -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Dsa.Generation

private theorem seedAddTail_step (n : Nat) {s : State} {Q : State → Prop}
    (h : WP isa (.block Impl.Dsa.X86_64.Generation.seedAddStep) s fun t =>
      t.zf = some (BitVec.ofNat 64 n == 0) ∧
      WP isa (Impl.Dsa.X86_64.Generation.seedAddTail n) t Q)
    (hn : n < 2 ^ 31) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAddTail (n + 1)) s Q := by
  obtain ⟨tr, u, he, hz, tr', v, hv, hq⟩ := h
  cases n with
  | zero =>
    cases hv with
    | block hb =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨_, _, .loopExit he (by simp [eval, hz]), hq⟩
  | succ n =>
    have hne : (BitVec.ofNat 64 (n + 1) == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have he := congrArg BitVec.toNat h
      change (n + 1) % 2 ^ 64 = 0 at he
      omega_arith
    exact ⟨_, _, .loopNext he (by simp only [eval, hz, hne, Option.map_some]; rfl) hv, hq⟩

private theorem seedAddTail_ok (bs : List Byte) {s : State} {rp op : Addr} {carry : Nat}
    (hlen : bs.length < 2 ^ 31)
    (hcount : s.gpr .rdx = BitVec.ofNat 64 bs.length) (hc : carry < 2 ^ 32)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAddTail bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length =
        Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.rax, .rcx, .rdx] s t := by
  induction bs using List.reverseRecOn generalizing s carry with
  | nil =>
    refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t = s) (by xrun) rfl) fun t ⟨rfl, hk⟩ => ?_
    exact ⟨rfl, fun _ _ => rfl, hk⟩
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hlen hcount hrd hwr hbytes hsep ⊢
    have hb : s.mem (off rp bs.length) = b := by
      simpa using hbytes bs.length (by omega_arith)
    refine seedAddTail_step bs.length ?_ (by omega_arith)
    refine WP.mono (seedAddStep_ok hc hrp hop hcarry hcount (hrd _ (by omega_arith)) (hwr _ (by omega_arith)) hb)
      fun u ⟨hcu, hcountu, hzu, hmu, ku⟩ => ?_
    refine ⟨hzu, ?_⟩
    have hru : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
      intro i hi
      rw [ku.2.1, ku.2.2]
      exact hrd i (by omega_arith)
    have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
      intro i hi
      rw [ku.2.2]
      exact hwr i (by omega_arith)
    have hbu : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
      intro i hi
      rw [hmu, WriteBytes.writeW8_apply, ite_eq_right (hsep i (by omega_arith) bs.length (by omega_arith)), hbytes i (by omega_arith)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    have hcp : (b.toNat + carry) / 256 < 2 ^ 32 := by
      have := b.isLt
      omega_arith
    refine WP.mono (ih (by omega_arith) hcountu hcp ((ku.gpr (by decide)).trans hrp)
      ((ku.gpr (by decide)).trans hop) hcu hru hwu hbu
      (fun i hi j hj => hsep i (by omega_arith) j (by omega_arith))) fun t ⟨hout, hf, kt⟩ => ?_
    refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [seedAdd_snoc]
      have hl : t.mem (off op bs.length) = BitVec.ofNat 8 (b.toNat + carry) := by
        rw [hf _ (fun i hi => Offset.add_ofNat_ne op (by omega_arith) (by omega_arith) (by omega_arith)),
          hmu, WriteBytes.writeW8_apply, ite_eq_left rfl]
      apply List.ext_getElem
      · simp [bytesAt_length, encodeBE_length]
      · intro i hi hi'
        have hil : i < bs.length + 1 := by simpa only [bytesAt_length] using hi
        by_cases hib : i < bs.length
        · have he := congrArg (fun xs : List Byte => xs[i]?) hout
          simpa [Spec.Rsa.bytesAt, off, hib, List.getElem?_append, encodeBE_length] using he
        · have hie : i = bs.length := by omega_arith
          subst i
          simpa [Spec.Rsa.bytesAt, off, List.getElem_append, encodeBE_length] using hl
    · intro a ha
      rw [hf a (fun i hi => ha i (by omega_arith)), hmu, WriteBytes.writeW8_apply,
        ite_eq_right (ha bs.length (by omega_arith))]

private theorem seedAddUnrolled_ok (bs : List Byte) {s : State} {rp op : Addr} {carry : Nat}
    (hlen : bs.length < 2 ^ 31) (hc : carry < 2 ^ 32)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAddUnrolled bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length =
        Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.rax, .rcx] s t := by
  induction bs using List.reverseRecOn generalizing s carry with
  | nil =>
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t = s) (by xrun) rfl) fun t ⟨rfl, hk⟩ => ?_
    exact ⟨rfl, fun _ _ => rfl, hk⟩
  | append_singleton bs b ih =>
    simp only [List.length_append, List.length_singleton] at hlen hrd hwr hbytes hsep ⊢
    have hb : s.mem (off rp bs.length) = b := by
      simpa using hbytes bs.length (by omega_arith)
    refine WP.seq (WP.mono (seedAddByte_ok hc hrp hop hcarry (hrd _ (by omega_arith)) (hwr _ (by omega_arith)) hb)
      fun u ⟨hcu, hmu, ku⟩ => ?_)
    have hru : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
      intro i hi
      rw [ku.2.1, ku.2.2]
      exact hrd i (by omega_arith)
    have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
      intro i hi
      rw [ku.2.2]
      exact hwr i (by omega_arith)
    have hbu : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
      intro i hi
      rw [hmu, WriteBytes.writeW8_apply, ite_eq_right (hsep i (by omega_arith) bs.length (by omega_arith)), hbytes i (by omega_arith)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    have hcp : (b.toNat + carry) / 256 < 2 ^ 32 := by
      have := b.isLt
      omega_arith
    refine WP.mono (ih (by omega_arith) hcp ((ku.gpr (by decide)).trans hrp)
      ((ku.gpr (by decide)).trans hop) hcu hru hwu hbu
      (fun i hi j hj => hsep i (by omega_arith) j (by omega_arith))) fun t ⟨hout, hf, kt⟩ => ?_
    refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
    · rw [seedAdd_snoc]
      have hl : t.mem (off op bs.length) = BitVec.ofNat 8 (b.toNat + carry) := by
        rw [hf _ (fun i hi => Offset.add_ofNat_ne op (by omega_arith) (by omega_arith) (by omega_arith)),
          hmu, WriteBytes.writeW8_apply, ite_eq_left rfl]
      apply List.ext_getElem
      · simp [bytesAt_length, encodeBE_length]
      · intro i hi hi'
        have hil : i < bs.length + 1 := by simpa only [bytesAt_length] using hi
        by_cases hib : i < bs.length
        · have he := congrArg (fun xs : List Byte => xs[i]?) hout
          simpa [Spec.Rsa.bytesAt, off, hib, List.getElem?_append, encodeBE_length] using he
        · have hie : i = bs.length := by omega_arith
          subst i
          simpa [Spec.Rsa.bytesAt, off, List.getElem_append, encodeBE_length] using hl
    · intro a ha
      rw [hf a (fun i hi => ha i (by omega_arith)), hmu, WriteBytes.writeW8_apply,
        ite_eq_right (ha bs.length (by omega_arith))]


private theorem seedAddLoop_ok (bs : List Byte) {s : State} {rp op : Addr} {carry : Nat}
    (hlen : bs.length < 2 ^ 31) (hc : carry < 2 ^ 32)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa (.seq (.block [.mov32 .rdx (.imm (BitVec.ofNat 32 bs.length))])
      (Impl.Dsa.X86_64.Generation.seedAddTail bs.length)) s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length =
        Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.rax, .rcx, .rdx] s t := by
  refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.gpr .rdx = BitVec.ofNat 64 bs.length ∧ t.mem = s.mem) (by
      xrun
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_arith) rfl)
    fun t ⟨⟨hd, hm⟩, hk⟩ => ?_)
  refine WP.mono (seedAddTail_ok bs hlen hd hc
    ((hk.gpr (by decide)).trans hrp) ((hk.gpr (by decide)).trans hop)
    ((hk.gpr (by decide)).trans hcarry)
    (fun i hi => by rw [hk.2.1, hk.2.2]; exact hrd i hi)
    (fun i hi => by rw [hk.2.2]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hbytes i hi) hsep) fun u ⟨out, hf, ku⟩ =>
      ⟨out, fun a ha => (hf a ha).trans (congrFun hm a), (hk.trans ku).mono (by decide)⟩

theorem seedAdd_ok (bs : List Byte) {s : State} {rp op : Addr} {carry : Nat}
    (hlen : bs.length < 2 ^ 31) (hc : carry < 2 ^ 32)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.seedAdd bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length =
        Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + carry) ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.rax, .rcx, .rdx] s t := by
  unfold Impl.Dsa.X86_64.Generation.seedAdd
  split
  · exact WP.mono (seedAddUnrolled_ok bs hlen hc hrp hop hcarry hrd hwr hbytes hsep)
      fun _ ⟨out, frame, keep⟩ => ⟨out, frame, keep.mono (by decide)⟩
  · exact seedAddLoop_ok bs hlen hc hrp hop hcarry hrd hwr hbytes hsep

end VG.Proof.Dsa.X86_64.Generation
