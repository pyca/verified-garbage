module

import VerifiedGarbage.Proof.Mont.X86.Square.RedPtr
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def redEnd : Prog isa := .seq
  (.ite .b (.block [.mov .ebx (.reg .esi)]) (.block []))
  (.block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)])

theorem redEnd_ok {s : State} {W : Addr} {L S N k l : Nat}
    (hw : Ws s W L) (scr : S+52+4*N<L) (ln : l≤N)
    (edi : PtrAt s W .edi S) (cx : PtrAt s W .ecx (S+52+4*l))
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) (bx : s.gpr .ebx = BitVec.ofNat 32 (4*N))
    (cf : s.cf = some (decide (k<N))) :
    WP isa redEnd s fun t =>
      PtrAt t W .ebx (S+52+4*min k N) ∧ t.cf = some (decide (l<min k N)) ∧
      t.mem = s.mem ∧ Keeps [.ebx] s t ∧ t.xmm = s.xmm := by
  have select : WP isa (.ite .b (.block [.mov .ebx (.reg .esi)]) (.block [])) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (4*min k N) ∧ t.mem = s.mem ∧ Keeps [.ebx] s t ∧ t.xmm = s.xmm := by
    refine WP.ite (decide (k<N)) (by change s.cf = _; exact cf) ?_ ?_
    · intro yes
      have lt : k<N := of_decide_eq_true yes
      refine VG.X86.Wp.cons rfl (WP.block_nil ?_)
      have u := VG.X86.Wp.Upd.setReg s .ebx (s.gpr .esi)
      exact ⟨by rw [u.gpr, si, Nat.min_eq_left (by omega)], rfl, u.keeps, rfl⟩
    · intro no
      have le : N≤k := by have := of_decide_eq_false no; omega
      exact WP.block_nil ⟨by rw [Nat.min_eq_right le]; exact bx, rfl, Keeps.refl _ _, rfl⟩
  unfold redEnd
  refine WP.seq (WP.mono select fun t1 ⟨bx1, m1, K1, x1⟩ => ?_)
  have body : WP isa (.block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)])
      t1 fun t => PtrAt t W .ebx (S+52+4*min k N) ∧ t.cf = some (decide (l<min k N)) ∧
        t.mem = t1.mem ∧ Keeps [.ebx] t1 t := by
    refine wp_addS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => wp_cmpCF rfl fun t4 f4 cf4 => WP.block_nil ?_
    have ei : t1.gpr .edi = BitVec.ofNat 32 (W.toNat+S) := by
      apply BitVec.eq_of_toNat_eq
      rw [K1.1 _ (by decide), edi, BitVec.toNat_ofNat]
    have b3 : t3.gpr .ebx = BitVec.ofNat 32 (W.toNat+S+52+4*min k N) := by
      rw [u3.gpr, u2.gpr, bx1, ei]
      change (BitVec.ofNat 32 (4*min k N)+BitVec.ofNat 32 (W.toNat+S))+BitVec.ofNat 32 52 = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega
    have c3 : (t3.gpr .ecx).toNat = W.toNat+(S+52+4*l) := by
      rw [u3.other _ (by decide), u2.other _ (by decide), K1.1 _ (by decide), cx, Nat.mod_eq_of_lt (by have := hw.nowrap; omega)]
    refine ⟨?_, ?_, f4.mem.trans (u3.mem.trans u2.mem), u2.keeps.trans (u3.keeps.trans (f4.keeps _))⟩
    · rw [PtrAt, f4.gpr, b3, BitVec.toNat_ofNat]; congr 1; omega
    · rw [cf4, c3, b3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hw.nowrap; have := Nat.min_le_right k N; omega)]
      have e : W.toNat+(S+52+4*l)<W.toNat+S+52+4*min k N ↔ l<min k N := by omega
      simp only [e]
  exact WP.mono (scalar_frame (by simp [scalar]) body)
    fun t ⟨⟨b, cf', mem, keep⟩, xmm⟩ => ⟨b, cf', mem.trans m1, K1.trans keep, xmm.trans x1⟩

end VG.Proof.Mont.X86.Square
