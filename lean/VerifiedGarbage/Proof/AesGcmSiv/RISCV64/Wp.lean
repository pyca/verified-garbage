module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# AES-GCM-SIV on RISC-V: arithmetic and the arguments of calls

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Wp.lean`): shifts and differences of small
numbers as 64-bit words; and the arguments of `vg_aes_ctr32` from the
environment (`cargs`): the encryption key's schedule at `W + 256` or the
key-generating key's at `K`, the counter block at `W + 112`, `k` blocks at
`Q` and the working space at `W + 1792`.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64
open VG.Proof.AesGcm.RISCV64 (CtrCall LoopOut)

theorem wp_and {s : State} {is : List Instr} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Steps.Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Steps.WP.cons exec_logic (k _ (Steps.Upd.write _ _ _))

theorem ofNat_shl (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  rw [Nat.mul_comm]

theorem ofNat_lsr {a : Nat} (k : Nat) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- What the copy and XOR loops keep. -/
theorem PK.ofLoop {s s' : State} {S D : Addr} {n : Nat} (O : LoopOut s S D n s') : PK s s' :=
  ⟨O.keeps.1, O.keeps.2.1, O.keeps.2.2, fun r hr => by
    have h : r ≠ .t0 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 := by
      revert r; decide
    exact O.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

/-- Two writes of the same register. -/
theorem upd2 {s t u : State} {d : Reg} {v w w' : BitVec 64} (u₁ : Steps.Upd s t d v)
    (u₂ : Steps.Upd t u d w) (h : w = w') : Steps.Upd s u d w' :=
  ⟨u₂.gpr.trans h, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Gcm.blockAt m' p = Spec.Gcm.blockAt m p := by
  rw [Spec.Gcm.blockAt, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_frame16 hf hd]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Gcm.blocksAt m' p n = Spec.Gcm.blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, Proof.Cmac.bytesAt_frame hf hd hn]

theorem setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The arguments of `vg_aes_ctr32`: the schedule of `R` rounds at `K'`, the
counter block at `W + 112`, `k` blocks at `Q`, which it may write, and the
working space at `W + 1792`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {K' : Addr}
    (hK : Covers [⟨K', 240⟩] (s.rd ++ s.wr)) (hKw : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 112, 16⟩)
    (hKs : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1792, 2048⟩)
    {Q : Addr} {k : Nat} (hqk : (⟨K', 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩)
    (hqc : (⟨c.W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint ⟨Q, 16 * k⟩)
    (hqs : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1792, 2048⟩)
    (hqw : Covers [⟨Q, 16 * k⟩] s.wr) (hfit : Q.toNat + 16 * k ≤ 2 ^ 64) (hk : k < 2 ^ 64)
    (a0 : s.gpr .a0 = K') (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R) (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 112)
    (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k) (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 1792) :
    CtrCall s K' (c.W + BitVec.ofNat 64 112) Q (c.W + BitVec.ofNat 64 1792) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := by rcases L.rounds with h | h <;> simp [h]
  n_lt := hk
  kc := hKw
  kd := hqk
  ks := hKs
  cd := hqc
  cs := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := hqs
  fit := hfit
  reads := Covers.append_left (Covers.cons hK Covers.nil)
    (Covers.cons (E.perm.wCR (by decide)) (Covers.cons (Covers.right hqw) (Covers.cons (E.perm.wCR (by decide))
      Covers.nil)))
  writes := Covers.cons (E.perm.wC (by decide)) (Covers.cons hqw (Covers.cons (E.perm.wC (by decide)) Covers.nil))

end VG.Proof.AesGcmSiv.RISCV64
