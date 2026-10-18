module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega

/-! # Check a complete seed or h chunk without cursor overflow -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem chunkCheck_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used total : Nat}
    (ht : slots.total < 37) (hu : slots.used < 37) (hw : width < 2 ^ 31)
    (hused : W slots.used = BitVec.ofNat 64 used) (htotal : W slots.total = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) :
    WP isa (.block (chunkCheck slots width)) s fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) :=
    by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax)] using hle)]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax), Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 64)]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.mem = s.mem) (by
    xrun [chunkCheck, ea_sp, L.rsp,
      L.ld (d := 8 * slots.total) (by unfold frameBytes; omega),
      L.ld (d := 8 * slots.used) (by unfold frameBytes; omega),
      R.slot (d := 8 * slots.total) (k := slots.total) rfl ht htotal,
      R.slot (d := 8 * slots.used) (k := slots.used) rfl hu hused, sx_ofNat hw, hsub]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : width < 2 ^ 64)]) rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
