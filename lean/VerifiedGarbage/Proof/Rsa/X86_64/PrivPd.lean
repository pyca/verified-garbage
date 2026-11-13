module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPc
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precomputed_checked`

`r₃` kept in its slot, and `M^e mod n` written to `out` (`pd_stage`), for
whatever `M` holds.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem arg_in {s t : State} (hp : PreF X s) (he : Env s t) {j : Nat} (hj : j < 14) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
    rw [he.rd, hp.hrd]; simp),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem word_wo0 (m : Mem) (base : Addr) (v : BitVec 64) {d' : Nat} (h : 8 ≤ d') (hd' : d' + 8 ≤ 4096) :
    (m.writeW base v).readW (off base d') 64 = m.readW (off base d') 64 := by
  have := word_wo m base v (d := 0) (d' := d') (.inl (by omega_arith)) (by decide) hd'
  simpa only [Bignum.word, off, BitVec.add_zero] using this

theorem arg_wo0 {s : State} (m : Mem) (v : BitVec 64) {j : Nat} (hj : j < 14) :
    (m.writeW (fb s) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  have := arg_wo (s := s) m v (d := 0) (by decide) hj
  simpa only [off, BitVec.add_zero] using this

/-! ## The call -/

/-- `M` in the frame, `k` bytes. -/
def mR (s : State) : Region := ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩

theorem mR_sub {s : State} (hp : PreF X s) : Region.Sub (mR s) (stkR s) :=
  frame_sub s (by have := hp.k2; unfold oM frameBytes; omega_arith)

/-- What it writes: `out` and the working space. -/
def pdWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, scrR s]

theorem word_self0 (m : Mem) (base : Addr) (v : BitVec 64) : word (m.writeW base v) base 0 = v := by
  have := word_writeW_self m base 0 v
  simpa only [off, BitVec.add_zero] using this

/-- Bytes of the frame at `d`, kept by a call's return address. -/
theorem entry_bytes {s t : State} (hsp : t.gpr .rsp = fb s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) d) n = Spec.Rsa.bytesAt t.mem (off (fb s) d) n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => (callEntry_frame hsp).bytes (R := ⟨off (fb s) d, n⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (ret_disjoint s h).symm)
    (by dsimp only; unfold frameBytes at h; omega_arith) (List.mem_range.mp hi)

end VG.Proof.Rsa.X86_64
