module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.State
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.State
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce

/-!
# Poly1305 on RISC-V: `blocks`

As on AArch64 (`Proof/Poly1305/AArch64/Radix64/Blocks.lean`): the loop
invariant says that the accumulator in the registers is that of the message
on entry followed by the blocks absorbed so far, modulo `p`; the epilogue
reduces and stores it. The code writes only temporaries and argument
registers, and the memory only in the state's accumulator.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The absorbing of a block, with the key from `Keys`. -/
theorem absorb_key_ok (s : State) (b : Reg) (off : Nat) (pad : Bool) (wide : Bool) {R : Nat}
    (hk : Keys R s)
    (ho : off + 15 < 2048)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (off + 8)) 8)
    (hal : wide = true → (s.gpr b + BitVec.ofNat 64 off).toNat % 8 = 0)
    (hb : b ∉ absorbRegs := by decide) :
    WP isa (.block (absorb b off pad wide)) s fun s' =>
      (Bounds s → hv s' % P =
        ((hv s + (word s.mem (s.gpr b) off + 2 ^ 64 * word s.mem (s.gpr b) (off + 8) +
          2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  obtain ⟨q, hr0, hr1, hq, hs1, hr⟩ := hk
  simpa only [← hr, Bounds] using absorb_ok s b off pad wide hr0 hr1 hq hs1 ho h0 h8 hal hb

theorem bounds_eq {s s' : State} {rs : List Reg} (h : Keeps rs s s')
    (hr : H0 ∉ rs ∧ H1 ∉ rs ∧ H2 ∉ rs := by decide) :
    hv s' = hv s ∧ (Bounds s → Bounds s') := by
  simp only [hv, val3, Bounds, h.1 _ hr.1, h.1 _ hr.2.1, h.1 _ hr.2.2]
  exact ⟨trivial, id⟩

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev blR : Region := ⟨bp s₀, 16 * nb s₀⟩
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  st_al : (st s₀).toNat % 8 = 0

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksRISCV64.pre s₀) : BPre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  have := (bp s₀).isLt
  by_contra h
  refine hp.st_bl (st s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, Nat.zero_add, Nat.reduceLeDiff]) ?_
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [h, this]

theorem blk_contains {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := hp.nb_lt
  rw [blkAddr, Offset.add_add]
  exact contains_off (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

end BPre

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value (m : Mem) (p : Addr) :
    word m p 0 + 2 ^ 64 * word m p (0 + 8) + 2 ^ 128 * true.toNat =
      leNum (bytesAt m p 16 ++ [0x01]) := by
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) 16 := by
  simp only [blks, blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

/-! ## The loop -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  keys : Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ Bounds s

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  a3 : s.gpr .a3 = blkAddr s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

/-- The two instructions after a block. -/
theorem advance_ok (s : State) :
    WP isa (.block [.addi .a3 .a3 16, .addi .a2 .a2 (-1)]) s fun s' =>
      s'.gpr .a3 = s.gpr .a3 + BitVec.ofNat 64 16 ∧ s'.gpr .a2 = s.gpr .a2 - BitVec.ofNat 64 1 ∧
      Keeps [.a3, .a2] s s' := by
  refine Steps.wp_addi (imm := 16) (by decide) fun s₁ u₁ =>
    Steps.wp_subi (imm := 1) (by decide) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
    fun r hr => ?_, by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr],
    by rw [u₂.sp, u₁.sp]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₂.other r hr.2, u₁.other r hr.1]

theorem body_ok {s₀ : State} (hp : BPre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa (body false) s fun s' =>
      (isa.eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (isa.eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.a3, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hab := absorb_key_ok s .a3 0 true false hL.keys (by decide) (hin 0 (by decide))
    (hin (0 + 8) (by decide)) (fun h => by cases h)
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hc : Common s₀ (i + 1) s₂ := by
    refine ⟨?_, Keeps.keys hL.keys k, ?_, ?_, ?_, fun hA => ?_⟩
    · rw [k.gpr' (r := .a0), hL.a0]
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2.1, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv₀, hb⟩ := hL.acc hA
      obtain ⟨hv', hb'⟩ := ha hb
      obtain ⟨e₂, b₂⟩ := bounds_eq k₂
      refine ⟨?_, b₂ hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by
        simp only [blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [e₂, hv', hL.a3, hL.mem, block_value, mod_step hv₀, blks_succ,
        Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hx2 : s₂.gpr .a2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .a2), hL.a2, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have := hp.nb_lt
  have hev := Steps.eval_nonzero_ofNat s₂ .a2 (k := nb s₀ - (i + 1)) (by omega_using [this]) hx2
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, show nb s₀ - (i + 1) = 0 by omega_using [hlast]]; rfl, hlast ▸ hc⟩
  · right
    refine ⟨by rw [hev, decide_eq_true (show nb s₀ - (i + 1) ≠ 0 by omega_using [hi, hlast])],
      by omega_using [hi, hlast], { hc with a3 := ?_, a2 := hx2 }⟩
    rw [a₁, k₁.gpr' (r := .a3), hL.a3, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]

/-! ## The epilogue -/

/-- The memory written: the accumulator only. -/
theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block (reduce ++ storeH)) s fun s' => Proof.Poly1305.blocksRISCV64.post s₀ s' := by
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .a0 = st s₀ := by rw [k₁.gpr', hc.a0]
  refine WP.mono (storeH_ok s₁ (by
    rw [k₁.2.2.2.1, hc.wr, hp.wr, x0₁]; exact List.mem_singleton_self _) (by rw [x0₁]; exact hp.st_al))
    fun s₂ ⟨m₂, _, _, _, _⟩ => ?_
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hc.acc hA
  have hN := hr hb
  have mem₁ : s₁.mem = s₀.mem := by rw [k₁.2.1, hc.mem]
  rw [x0₁, mem₁] at m₂
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact storeHm_frame (Frame.refl _ _) _ _ _
  have hlen := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₂, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    change hv s₁ = _
    rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ (Proof.Poly1305.blocksRISCV64.post s₀) := by
  rw [blocks]
  refine WP.seq (Steps.wp_mv fun s₁ u₁ => WP.mono (setup_ok s₁ (by
    rw [u₁.other _ (by decide), u₁.rd, u₁.wr, hp.wr]
    exact List.mem_append_right _ (List.mem_singleton_self _))
    (by rw [u₁.other _ (by decide)]; exact hp.st_al)) fun s₂ h₂ => ?_)
  obtain ⟨hk, ha, k⟩ := h₂
  have k₁ : Keeps [.a3] s₀ s₁ := ⟨fun r hr => u₁.other r (by simpa using hr), u₁.mem, u₁.rd, u₁.wr,
    u₁.sp⟩
  have K := k₁.trans k
  have hm₁ : Rk s₁.mem (s₁.gpr .a0) = Rn s₀ := by rw [k₁.2.1, k₁.gpr' (r := .a0)]
  have hA₁ : A0 s₁ = A0 s₀ := by simp only [A0, st, k₁.2.1, k₁.gpr' (r := .a0)]
  rw [hm₁] at hk
  rw [hA₁] at ha
  have hc₀ : Common s₀ 0 s₂ := ⟨K.gpr' (r := .a0), hk, K.2.2.1, K.2.2.2.1, K.2.1,
    fun hA => by
      obtain ⟨e, b⟩ := ha hA
      refine ⟨?_, b⟩
      rw [e, show blks s₀ 0 = [] by simp only [blks, bytesAt, Nat.mul_zero, List.range_zero,
        List.map_nil], Poly1305.absorbAll_nil]⟩
  have x2₂ : s₂.gpr .a2 = s₀.gpr .a2 := K.gpr' (r := .a2)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc₃ => epilogue_ok hp hc₃)
  refine WP.ite (s₂.gpr .a2 == 0) (Steps.eval_zero _ _) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by
      simp only [x2₂, beq_iff_eq] at h
      simp only [nb, h]; rfl
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [x2₂, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa (body false) s (fun s' =>
        (isa.eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (isa.eval (.nonzero .a2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₂ :=
      { hc₀ with
        a3 := by rw [k.gpr' (r := .a3), u₁.gpr]; simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]
        a2 := by rw [x2₂]; simp only [nb, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hL₀⟩

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksRISCV64.pre s) :
    ∃ t s', Exec isa blocks s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.blocksRISCV64.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (blocks_correct (BPre.of s hs)) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksRISCV64.pre
    Proof.Poly1305.blocksRISCV64.pub blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_verified : Verified RISCV64.target blocks Proof.Poly1305.blocksRISCV64 :=
  ⟨blocks_ok, blocks_ct, ⟨blocksSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide⟩⟩

end VG.Proof.Poly1305.RISCV64
