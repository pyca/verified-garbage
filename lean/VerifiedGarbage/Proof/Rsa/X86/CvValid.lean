module

public import VerifiedGarbage.Proof.Rsa.X86.CvResult
public import VerifiedGarbage.Proof.Rsa.X86.CvDispatch
public import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch

/-! # CRT dispatch follows the public modulus length -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.CrtValues

theorem width_ok {s : State} {len : Nat} (bound : len ≤ 1024)
    (count : readSrc s (.mem (PublicFn.argument 7)) = some (BitVec.ofNat 32 len)) :
    WP isa (.block [.mov .eax (.mem (PublicFn.argument 7)), .alu .add .eax (.imm 7), .shift .shr .eax 3]) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  refine wp_movS count fun u A _ => ?_
  refine wp_addS rfl fun v B _ => ?_
  refine wp_shr (by decide) fun t C _ => WP.block_nil ?_
  refine ⟨?_, C.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans C.keeps⟩
  rw [C.gpr, B.gpr, A.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Spec.Rsa.modulusWords, show (7 : BitVec 32).toNat = 7 from rfl]
  omega


theorem valid_ok {g : CallGeometry} {s : State} (h : Inputs g s)
    (lo : 64 ≤ (g.args 7).toNat) (hi : (g.args 7).toNat ≤ 1024)
    (width : g.n = Spec.Rsa.modulusWords (g.args 7).toNat) :
    WP isa valid s fun t => Inputs g t ∧ ArithmeticPost g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold valid
  refine WP.seq (WP.mono (width_ok hi (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (h.arguments 7 (by decide)).readSrc)) fun u ⟨w, m, k⟩ => ?_)
  apply dispatch_ok PublicFn.widths (n := g.n)
    (by rw [width]; exact publicWidths_member lo hi)
    (by intro n hn; simp only [PublicFn.widths, List.mem_map, List.mem_range] at hn
        obtain ⟨i, hi, rfl⟩ := hn; omega)
    (by rw [width]; exact w)
  intro v kv mv
  have mem : v.mem = s.mem := mv.trans m
  have keeps : Keeps [.eax] s v := k.trans (kv.mono (by simp))
  have hv := h.after keeps (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.mono (sized_ok hv) fun t ⟨ht, result, frame, rest⟩ => ?_
  exact ⟨ht, mem ▸ result, mem ▸ frame, (keeps.mono (by decide)).trans rest⟩

end VG.Proof.Rsa.X86.CrtValues
