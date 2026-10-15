module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Dsa.X86.Bytes

/-! # Encoding arithmetic results into persistent DSA scratch -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem outside_rebase {base : Addr} {out len : Nat} {m m' : Mem}
    (h : Outside (off base out) 0 len m m') (hb : out + len ≤ 2 ^ 64) :
    Outside base out len m m' := by
  intro x hx
  apply h x
  have H := Offset.lt_iff x base hb
  change ofs (off base out) x < len ↔ out ≤ ofs base x ∧ ofs base x < out + len at H
  right
  simp only [Nat.zero_add]
  omega

theorem coreStore_ok {s : State} {base : Addr} {size n len output : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (ha : slot n 6 + 8 * n ≤ size) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (ho : output + len ≤ size) (hsep : slot n 6 + 8 * n ≤ output ∨ output + len ≤ slot n 6) :
    WP isa (.block (Core.store n len output)) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len (wordsVal s.mem base (slot n 6) n) ∧
      Keeps [.esi, .eax, .ecx, .edx] s t ∧ Outside base output len s.mem t.mem := by
  have nw := hs.nowrap
  have fit : base.toNat + output < 2 ^ 32 := by omega
  have out32 : output < 2 ^ 32 := by omega
  unfold Core.store
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (pointer_ok hs hz (.local output)) fun u ⟨Pu, Ku, Mu⟩ => ?_)
  have pa : (u.gpr .esi).setWidth 64 = off base output := by
    rw [Pu, pointerValue]
    have eq := addr_eq (x := s.gpr .edi) (k := output) (by rw [hs.edi_toNat]; exact fit)
    rw [hs.edi] at eq
    exact eq
  have pn : (u.gpr .esi).toNat = base.toNat + output := by
    rw [Pu, pointerValue, BitVec.toNat_add, BitVec.toNat_ofNat, hs.edi_toNat,
      Nat.mod_eq_of_lt out32, Nat.mod_eq_of_lt fit]
  simp only [List.singleton_append]
  refine wp_movS rfl fun v uv _ => ?_
  have Kv : Keeps [.esi, .ecx] s v := (Ku.mono (by decide)).widen uv.keeps
  have pv : v.gpr .esi = u.gpr .esi := uv.other _ (by decide)
  refine WP.mono (storeComponent_ok (hs.of_keeps Kv (by decide)) true uv.gpr ha h4 hlen
    (by rw [pv, pn]; omega)
    (by
      intro e k hek
      rw [pv, pa]
      change InRegions v.wr (base + BitVec.ofNat 64 output + BitVec.ofNat 64 e) k
      rw [Offset.add_add]
      exact (hs.of_keeps Kv (by decide)).write (by omega))
    (by rw [pv, pa]; exact Offset.disjoint base hsep (by omega) (by omega)))
    fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Kv.mono (by decide)).widen Kt, ?_⟩
  · simpa only [pv, pa, uv.mem, Mu, ite_true] using Vt
  · rw [pv, pa, uv.mem, Mu] at Ot
    exact outside_rebase Ot (by omega)

end VG.Proof.Dsa.X86
