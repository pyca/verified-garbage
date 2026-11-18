module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.ListSnoc

/-! ### `Dsa.X86_64.Generation.SeedAdd`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Generation.SeedByte`, which only this module used -/

section

/-! # Carry propagation for one wrapped-seed byte -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem byte_add (c : Nat) (b : Byte) :
    BitVec.ofNat 64 c + b.setWidth 64 = BitVec.ofNat 64 (b.toNat + c) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem seedAddByte_ok {s : State} {rp op : Addr} {i carry : Nat} {b : Byte}
    (hc : carry < 2 ^ 32) (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hrd : InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : InRegions s.wr (off op i) 1) (hb : s.mem (off rp i) = b) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedAddByte i)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry)) ∧ Keep [.rax, .rcx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry))) ?_ rfl)
    fun _ ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  simp only [off] at hrd hwr hb
  xrun [Impl.Dsa.X86_64.Generation.seedAddByte, State.ea, hrp, hop, hcarry,
    BitVec.ofInt_natCast, off, hrd, hwr, hb, byte_add carry b]
  constructor
  · apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega_using [hc]
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []


/-- One iteration of the compact seed loop, indexed by its public count. -/
theorem seedAddStep_ok {s : State} {rp op : Addr} {i carry : Nat} {b : Byte}
    (hc : carry < 2 ^ 32) (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hcarry : s.gpr .rax = BitVec.ofNat 64 carry)
    (hcount : s.gpr .rdx = BitVec.ofNat 64 (i + 1))
    (hrd : InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : InRegions s.wr (off op i) 1) (hb : s.mem (off rp i) = b) :
    WP isa (.block Impl.Dsa.X86_64.Generation.seedAddStep) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.gpr .rdx = BitVec.ofNat 64 i ∧ t.zf = some (BitVec.ofNat 64 i == 0) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry)) ∧
      Keep [.rax, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((b.toNat + carry) / 256) ∧
      t.gpr .rdx = BitVec.ofNat 64 i ∧ t.zf = some (BitVec.ofNat 64 i == 0) ∧
      t.mem = s.mem.writeW (off op i) (BitVec.ofNat 8 (b.toNat + carry))) ?_ rfl)
    fun _ ⟨⟨hv, hd, hz, hm⟩, hk⟩ => ⟨hv, hd, hz, hm, hk⟩
  have hsub : BitVec.ofNat 64 (i + 1) - 1 = BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_add]; bv_omega_arith
  have hindex (a : Addr) : a + BitVec.ofNat 64 (i + 1) * (1#64) + BitVec.ofInt 64 (-1) = off a i := by
    simp only [off, BitVec.ofNat_add, BitVec.mul_one]
    bv_omega_arith
  xrun [Impl.Dsa.X86_64.Generation.seedAddStep, State.ea, hrp, hop, hcarry, hcount,
    hindex, hsub, hrd, hwr, hb, byte_add carry b]
  constructor
  · apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega_using [hc]
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []

end VG.Proof.Dsa.X86_64.Generation

end

end


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
  induction bs using VG.List.reverseRecOn generalizing s carry with
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
  induction bs using VG.List.reverseRecOn generalizing s carry with
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

end

end

/-! # Prepare the public seed offset for a p hash contribution -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem seedInputArgs_ok {s : State} {F S rp op : Addr} {offset j : Nat}
    (hj : j < 2 ^ 31) (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hrp : W 1 = rp) (hop : W 3 = op)
    (hoff : W 2 = BitVec.ofNat 64 offset) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedInputArgs j)) s fun t =>
      t.gpr .rsi = rp ∧ t.gpr .rdi = op ∧ t.gpr .rax = BitVec.ofNat 64 (offset + j) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .rax] s t := by
  refine WP.mono (WP.keep [.rsi, .rdi, .rax] (Q := fun t =>
      t.gpr .rsi = rp ∧ t.gpr .rdi = op ∧ t.gpr .rax = BitVec.ofNat 64 (offset + j) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩
  xrun [Impl.Dsa.X86_64.Generation.seedInputArgs, ea_sp, L.rsp,
    L.ld (d := 8) (by decide), L.ld (d := 16) (by decide), L.ld (d := 24) (by decide),
    R.slot (d := 8) (k := 1) rfl (by decide) hrp,
    R.slot (d := 16) (k := 2) rfl (by decide) hoff,
    R.slot (d := 24) (k := 3) rfl (by decide) hop]
  change BitVec.ofNat 64 offset + BitVec.signExtend 64 (BitVec.ofNat 32 j) = _
  rw [sx_ofNat hj, BitVec.ofNat_add]

/-- Place each digest in descending contribution order. -/
theorem hashCopyArgs_ok {s : State} {F S op : Addr} {len count j : Nat}
    (hlen : len = 20 ∨ len = 32) (hcount : count ≤ 11)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hop : W 4 = op) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.hashCopyArgs len count j)) s fun t =>
      t.gpr .rsi = off S oDig ∧ t.gpr .rdi = off op ((count - j) * len) ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .rcx, .rdx] s t := by
  have hoff : (count - j) * len < 2 ^ 31 := by rcases hlen with rfl | rfl <;> omega_using [hcount]
  have hs := L.slot
  simp only [VG.Proof.Bignum.word] at hs
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rsi = off S oDig ∧ t.gpr .rdi = off op ((count - j) * len) ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b, c, d, e⟩, hk⟩ => ⟨a, b, c, d, e, hk⟩
  xrun [Impl.Dsa.X86_64.Generation.hashCopyArgs, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := 32) (by decide), hs,
    R.slot (d := 32) (k := 4) rfl (by decide) hop]
  refine ⟨congrArg (fun x : BitVec 64 => S + x) (by decide), ?_, ?_, ?_⟩
  · change op + BitVec.signExtend 64 (BitVec.ofNat 32 ((count - j) * len)) = _
    rw [sx_ofNat hoff]
  all_goals rcases hlen with rfl | rfl <;> decide

end VG.Proof.Dsa.X86_64.Generation
