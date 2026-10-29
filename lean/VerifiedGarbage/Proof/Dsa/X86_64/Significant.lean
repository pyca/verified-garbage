module

public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # The public actual-width scan's first-nonzero selection -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The scan keeps the first nonzero byte and its remaining buffer width. -/
def scanNext (found : Nat × Byte) (remaining : Nat) (b : Byte) : Nat × Byte :=
  if found.1 = 0 ∧ b ≠ 0 then (remaining, b) else found

/-- Selection only changes the saved first-byte pair; it never writes memory. -/
theorem significantChoose_ok {s : State} {found : Nat × Byte} {remaining : Nat} {b : Byte}
    (h8 : s.gpr .r8 = BitVec.ofNat 64 found.1)
    (h9 : s.gpr .r9 = found.2.zeroExtend 64)
    (ha : s.gpr .rax = b.zeroExtend 64)
    (hc : s.gpr .rcx = BitVec.ofNat 64 remaining)
    (hz : s.zf = some (decide (found.1 = 0))) :
    WP isa Checks.significantChoose s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (scanNext found remaining b).1 ∧
      t.gpr .r9 = (scanNext found remaining b).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.rax, .r8, .r9] s t := by
  unfold Checks.significantChoose
  by_cases hf : found.1 = 0
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change VG.X86_64.eval .e s = some true
      simp only [VG.X86_64.eval, hz, hf, decide_true]
    · refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
        u.zf = some (b == 0) ∧ u.mem = s.mem ∧ u.gpr .rax = b.zeroExtend 64) ?_ rfl) fun u ⟨⟨huz, hum, hua⟩, hku⟩ => ?_)
      · have hbeq : (b.zeroExtend 64 == 0) = (b == 0) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq]
          constructor
          · intro h
            have h' := congrArg BitVec.toNat h
            change (b.setWidth 64).toNat = 0 at h'
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at h'
            exact BitVec.eq_of_toNat_eq h'
          · intro h; subst b; rfl
        xrun [ha, BitVec.and_self, hbeq]
      by_cases hb : b = 0
      · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
        · change VG.X86_64.eval .ne u = some false
          simp only [VG.X86_64.eval, huz, hb, beq_self_eq_true, Option.map_some, Bool.not_true]
        · have hn : scanNext found remaining b = found := by simp [scanNext, hb]
          rw [hn]
          exact ⟨(hku.gpr (by decide)).trans h8, (hku.gpr (by decide)).trans h9, hum,
            hku.mono (by decide)⟩
      · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
        · change VG.X86_64.eval .ne u = some true
          simp only [VG.X86_64.eval, huz, beq_eq_false_iff_ne.mpr hb, Option.map_some, Bool.not_false]
        · have hn : scanNext found remaining b = (remaining, b) := ite_eq_left ⟨hf, hb⟩
          rw [hn]
          refine WP.mono (WP.keep [.r8, .r9] (Q := fun t =>
            t.gpr .r8 = BitVec.ofNat 64 remaining ∧ t.gpr .r9 = b.zeroExtend 64 ∧ t.mem = u.mem)
            ?_ rfl) fun t ⟨⟨ht8, ht9, htm⟩, hkt⟩ =>
              ⟨ht8, ht9, htm.trans hum, (hku.trans hkt).mono (by decide)⟩
          have huc := (hku.gpr (show Reg.rcx ∉ [Reg.rax] by decide)).trans hc
          xrun [huc, hua]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    · change VG.X86_64.eval .e s = some false
      simp only [VG.X86_64.eval, hz, hf, decide_false]
    · have hn : scanNext found remaining b = found := by simp [scanNext, hf]
      rw [hn]
      exact ⟨h8, h9, rfl, Keep.refl _ _⟩

/-- One byte of the public scan preserves memory and advances exactly once. -/
theorem significantByte_ok {s : State} {p : Addr} {found : Nat × Byte} {remaining : Nat}
    (hsi : s.gpr .rsi = p) (hcx : s.gpr .rcx = BitVec.ofNat 64 remaining)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 found.1) (h9 : s.gpr .r9 = found.2.zeroExtend 64)
    (hr : InRegions (s.rd ++ s.wr) p 1)
    (hfound : found.1 < 2 ^ 64) (h1 : 1 ≤ remaining) (h64 : remaining < 2 ^ 64) :
    WP isa Checks.significantByte s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (remaining - 1) ∧
      t.gpr .r8 = BitVec.ofNat 64 (scanNext found remaining (s.mem p)).1 ∧
      t.gpr .r9 = (scanNext found remaining (s.mem p)).2.zeroExtend 64 ∧
      t.zf = some (decide (remaining = 1)) ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .r9, .rsi, .rcx] s t := by
  have e0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => BitVec.add_zero x
  unfold Checks.significantByte seqs
  refine WP.seq (WP.mono (WP.keep [.rax, .r8] (Q := fun u =>
    u.gpr .rax = (s.mem p).zeroExtend 64 ∧ u.gpr .r8 = BitVec.ofNat 64 found.1 ∧
    u.zf = some (decide (found.1 = 0)) ∧ u.mem = s.mem) ?_ rfl)
    fun u ⟨⟨hua, hu8, huz, hum⟩, hku⟩ => ?_)
  · xrun [State.ea, at0, hsi, e0, hr, h8, BitVec.and_self, ofNat_beq_zero hfound]
  have hu9 := (hku.gpr (show Reg.r9 ∉ [Reg.rax, Reg.r8] by decide)).trans h9
  have huc := (hku.gpr (show Reg.rcx ∉ [Reg.rax, Reg.r8] by decide)).trans hcx
  refine WP.seq (WP.mono (significantChoose_ok hu8 hu9 hua huc huz)
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hvsi := ((hku.trans hkv).gpr (show Reg.rsi ∉ [Reg.rax, Reg.r8] ++ [Reg.rax, Reg.r8, Reg.r9] by decide)).trans hsi
  have hvc := ((hku.trans hkv).gpr (show Reg.rcx ∉ [Reg.rax, Reg.r8] ++ [Reg.rax, Reg.r8, Reg.r9] by decide)).trans hcx
  have hsub := ofNat64_pred h1 h64
  have he : (BitVec.ofNat 64 (remaining - 1) == 0) = decide (remaining = 1) := by
    rw [ofNat_beq_zero (by omega), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (remaining - 1) ∧
    t.zf = some (decide (remaining = 1)) ∧ t.mem = v.mem) ?_ rfl)
    fun t ⟨⟨htsi, htc, htz, htm⟩, hkt⟩ =>
      ⟨htsi, htc, (hkt.gpr (by decide)).trans hv8, (hkt.gpr (by decide)).trans hv9,
        htz, (htm.trans hvm).trans hum, ((hku.trans hkv).trans hkt).mono (by decide)⟩
  xrun [hvsi, hvc, hsub, he]

end VG.Proof.Dsa.X86_64
