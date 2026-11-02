module

public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num0
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Numbers of `8 k` bytes in `k + 1` words on RISC-V

`loadNum0` (`loadNum0_ok`): the top word zero, then the `8 k` bytes by
`loadNum`. `storeNum` of a `k + 1`-word number's low `k` words writes its
`8 k` low bytes (`storeNum_low_ok`), which are the number's own when it is
below `2^(64 k)`, as P-192's numbers below `p` are.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Mont
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Ecdsa (bytesAt)
open VG.Spec.Weierstrass (ofBytes toBytes)

/-- `loadNum0`: the `8 k` bytes at `p + off`, big-endian, to the slot at `o`,
whose top word is zero. -/
theorem loadNum0_ok (k : Nat) {s : State} {base : Addr} {o : Nat} {p : Reg} {off : Nat}
    (hw : WsReg s base) (hp : p ∉ [Reg.t0, .t1]) (ho : o % 8 = 0) (ho' : o + 8 * (k + 1) ≤ 2048)
    (hoff : off + 8 * k ≤ 2048)
    (hin : ∀ j < k, InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 (off + 8 * j)) 8)
    (hsep : ∀ i < 8 * k, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (loadNum0 k o p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * (k + 1)) s.mem s'.mem ∧
      wordsVal s'.mem base o (k + 1) = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) (8 * k)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
  rw [loadNum0, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_
  have r₁ : Rest [.t0, .t1] s s₁ := u₁.rest (by decide)
  have hw₁ := hw.of_rest r₁
  refine sd_ws hw₁ (d := o + 8 * k) (by omega) (by omega) fun s₂ u₂ => ?_
  have r₂ : Rest [.t0, .t1] s s₂ := r₁.trans (u₂.rest _)
  have O₂ : Outside base (o + 8 * k) 8 s.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]; exact writeW_outside _ _ _ (by omega)
  have g₂ : s₂.gpr p = s.gpr p := r₂.gpr _ (by simp [hp.1, hp.2])
  refine WP.mono (loadNum_ok k (hw.of_rest r₂) (p := p) (off := off) (by simp [hp.1, hp.2]) ho (by omega)
    hoff (fun j hj => by rw [r₂.rd, r₂.wr, g₂]; exact hin j hj)
    (fun i hi => by rw [g₂]; exact hsep i hi))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ⟨r₂.trans r₃, (O₂.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega)), ?_⟩
  have e₃' : wordsVal s₃.mem base o k = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) (8 * k)) := by
    rw [e₃, g₂, bytesAt_out O₂ (by omega) (fun i hi => by rw [add_ofNat_add]; exact hsep i hi)]
  rw [wordsVal_succ_top, e₃', O₃.word (by omega) (by omega), u₂.mem, word_writeW_self, u₁.gpr]
  simp

open VG.WriteBytes in
/-- `storeNum` of the low `k` words of a `k + 1`-word number: its `8 k` low
bytes, under the mask, or zeros. -/
theorem storeNum_low_ok (c : Bool) (k : Nat) {s : State} {base : Addr} {a : Nat} {q : Reg} {off : Nat}
    (hw : WsReg s base) (hc : s.gpr .a7 = maskOf c) (hq : q ∉ [Reg.t0, .t1]) (ha : a % 8 = 0)
    (ha' : a + 8 * (k + 1) ≤ 2048) (hoff : off + 8 * k ≤ 2048)
    (hout : ∀ i < 8 * k, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + i)) 1)
    (hsep : ∀ i < 8 * k, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (storeNum k a q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes (8 * k) (if c then wordsVal s.mem base a (k + 1) else 0)) := by
  refine WP.mono (storeNum_ok c k hw hc hq ha (by omega) hoff hout hsep) fun s' ⟨r, m⟩ => ⟨r, ?_⟩
  rw [m]
  congr 1
  cases c
  · rfl
  · simp only [↓reduceIte]
    rw [wordsVal_succ_top, show 2 ^ (64 * k) = 2 ^ (8 * (8 * k)) by congr 1; omega, toBytes_mod]

end VG.Proof.Weierstrass.RISCV64
