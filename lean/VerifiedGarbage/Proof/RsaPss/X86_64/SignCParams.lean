module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncParams
public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS signing and verification on x86-64, around the encoding: the
parameters

From the modulus' first byte `n₀ ≠ 0` in `rax` and its length `k`, `emBitsB`
stores `emBits = 8 (k - 1) + log₂ n₀`, `emLen = ⌈emBits / 8⌉` and
`lo = k - emLen` to their slots (`emBitsB_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

/-- The seven compares of `emBitsB`. -/
def sbbChain : List Instr := [.alu .cmp .rax (.imm 2), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 4), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 8), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 16), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 32), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 64), .alu .sbb .rdx (.imm 0), .alu .cmp .rax (.imm 128), .alu .sbb .rdx (.imm 0)]

/-- What each compare of `sbbChain` subtracts: 1 if `x < c`. -/
abbrev cb (y : BitVec 64) (c : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.ofBool (decide (y.toNat < c.toNat)))

/-- The seven of them. -/
def cbSum (y : BitVec 64) : BitVec 64 :=
  cb y 2 + cb y 4 + cb y 8 + cb y 16 + cb y 32 + cb y 64 + cb y 128

theorem sub7 (d z a1 a2 a3 a4 a5 a6 a7 : BitVec 64) (hz : z = 0) :
    d - z - a1 - z - a2 - z - a3 - z - a4 - z - a5 - z - a6 - z - a7 =
      d - (a1 + a2 + a3 + a4 + a5 + a6 + a7) := by
  subst hz; simp [BitVec.sub_sub, BitVec.add_assoc]

theorem cbSum_table : ∀ x < 256, x ≠ 0 →
    ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ cbSum (BitVec.ofNat 64 x) = BitVec.ofNat 64 (7 - j) := by
  decide +kernel

theorem cbSum_eq {x : Nat} (hx : x < 256) (h0 : x ≠ 0) :
    cbSum (BitVec.ofNat 64 x) = BitVec.ofNat 64 (7 - Nat.log2 x) := by
  obtain ⟨j, _, hl, hu, he⟩ := cbSum_table x hx h0
  rw [he, RsaPss.log2_eq h0 hl hu]

/-- `rdx := 8 k - 1 - cbSum x`. -/
theorem sbbChain_ok (u : State) (x : BitVec 64) (d : BitVec 64) (hax : u.gpr .rax = x) (hdx : u.gpr .rdx = d) :
    WP isa (.block sbbChain) u fun u' => Keep [.rdx, .rax] u u' ∧ u'.mem = u.mem ∧ u'.gpr .rdx = d - cbSum x := by
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rdx = d - cbSum x) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [sbbChain, hax, hdx]
  rw [sub7 _ (BitVec.signExtend 64 0) _ _ _ _ _ _ _ (by decide)]
  simp only [cbSum, cb]
  rfl

/-- `emBits` from the modulus' length and first byte. -/
def ebV (k x : Nat) : Nat := 8 * (k - 1) + Nat.log2 x

theorem emBitsB_eq : emBitsB = ([.mov .rdx (.mem (sp sK)), .shift .shl .rdx 3, .alu .sub .rdx (.imm 1)] : List Instr) ++
    sbbChain ++ ([.store (sp sBits) .rdx, .mov .rax (.reg .rdx), .alu .add .rax (.imm 7), .shift .shr .rax 3,
      .store (sp sEml) .rax, .mov .r8 (.mem (sp sK)), .alu .sub .r8 (.reg .rax), .store (sp sLo) .r8] : List Instr) :=
  rfl

theorem emBitsB_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k x : Nat} (hk : W 17 = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hk2 : k ≤ 1024)
    (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block emBitsB) u fun u' => Lay u' F S ∧ Keep [.rdx, .rax, .r8] u u' ∧
      Rep u'.mem F S V (upd (upd (upd W 27 (BitVec.ofNat 64 (ebV k x))) 28
        (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)))) 26 (BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)))) := by
  have G := L.geo
  have hl8 : Nat.log2 x < 8 := (Nat.log2_lt h0).mpr (by omega)
  have heb : ebV k x ≤ 8 * k - 1 := by unfold ebV; omega
  have hel : Spec.RsaPss.emLength (ebV k x) ≤ k := by unfold Spec.RsaPss.emLength; omega
  rw [emBitsB_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun v => v.mem = u.mem ∧ v.gpr .rdx = BitVec.ofNat 64 (8 * k - 1)) ?_ rfl)
    fun v ⟨⟨hm, hd⟩, kv⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sK) (by decide), R.rd (d := sK) 17 rfl (by decide), hk]
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow]
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
    omega
  refine WP.mono (sbbChain_ok v (BitVec.ofNat 64 x) _ (by rw [kv.gpr (by decide)]; exact hax) hd)
    fun w ⟨kw, hmw, hdw⟩ => ?_
  have hdw' : w.gpr .rdx = BitVec.ofNat 64 (ebV k x) := by
    rw [hdw, cbSum_eq hx h0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    unfold ebV; omega
  have Lw : Lay w F S := L.congr ((kw.gpr (by decide)).trans (kv.gpr (by decide))) (kw.2.2.trans kv.2.2)
    (by rw [hmw, hm])
  have Rw : Rep w.mem F S V W := by rw [hmw, hm]; exact R
  have R1 := Rw.wf G (k := 27) (by decide) (BitVec.ofNat 64 (ebV k x))
  have R2 := R1.wf G (k := 28) (by decide) (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)))
  have R3 := R2.wf G (k := 26) (by decide) (BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)))
  rw [show off F (8 * 27) = off F sBits from rfl] at R1 R2 R3
  rw [show off F (8 * 28) = off F sEml from rfl] at R2 R3
  rw [show off F (8 * 26) = off F sLo from rfl] at R3
  have h17 : (((w.mem.writeW (off F sBits) (BitVec.ofNat 64 (ebV k x))).writeW (off F sEml)
      (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x))))).readW (off F sK) 64 = BitVec.ofNat 64 k := by
    have := R2.fr 17 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hk, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun y => y.mem = ((w.mem.writeW (off F sBits)
      (BitVec.ofNat 64 (ebV k x))).writeW (off F sEml) (BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)))).writeW
      (off F sLo) (BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)))) ?_ rfl) fun y ⟨hmy, ky⟩ => ?_
  · have h7 : (BitVec.ofNat 64 (ebV k x) + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 =
        BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)) := by
      have hb : ebV k x < 8192 := by unfold ebV at *; omega
      generalize ebV k x = e at hb ⊢
      rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 from rfl]
      unfold Spec.RsaPss.emLength
      bv_omega
    xrun [ea_sp, Lw.rsp, Lw.st (d := sBits) (by decide), Lw.st (d := sEml) (by decide), Lw.st (d := sLo) (by decide),
      Lw.ld (d := sK) (by decide), hdw', h7, h17, VG.Offset.ofNat_sub_ofNat hel]
  refine ⟨Lw.of_rep' Rw (hmy ▸ R3) (by simp [upd]) (ky.gpr (by decide)) ky.2.2,
    ((kv.trans kw).trans ky).mono (by decide), hmy ▸ R3⟩

end VG.Proof.RsaPss.X86_64
