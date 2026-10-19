module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.Layout

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

/-- Switch from the original seed to the wrapped-seed buffer without
changing any other hash-frame slot or scratch byte. -/
theorem useWrappedSeed_ok {s : State} {F S op : Addr}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hop : W 3 = op) :
    WP isa (.block Impl.Dsa.X86_64.Generation.useWrappedSeed) s fun t =>
      Rep t.mem F S V (upd W 27 op) ∧
      Outside F sLab 8 s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off F sLab) op) (by
    xrun [Impl.Dsa.X86_64.Generation.useWrappedSeed, ea_sp, L.rsp,
      L.ld (d := 24) (by decide), L.st (d := sLab) (by decide),
      R.slot (d := 24) (k := 3) rfl (by decide) hop]) rfl)
    fun t ⟨hm, hk⟩ => ?_
  refine ⟨?_, ?_, hk⟩
  · rw [hm]
    exact R.wf L.geo (by decide : 27 < nW) op
  · rw [hm]
    exact writeW_outside _ _ _ (by decide)

/-- Place each digest in descending contribution order. -/
theorem hashCopyArgs_ok {s : State} {F S op : Addr} {len count j : Nat}
    (hlen : len = 20 ∨ len = 32) (hcount : count ≤ 11)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hop : W 4 = op) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.hashCopyArgs len count j)) s fun t =>
      t.gpr .rsi = off S oDig ∧ t.gpr .rdi = off op ((count - j) * len) ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .rcx, .rdx] s t := by
  have hoff : (count - j) * len < 2 ^ 31 := by rcases hlen with rfl | rfl <;> omega
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
