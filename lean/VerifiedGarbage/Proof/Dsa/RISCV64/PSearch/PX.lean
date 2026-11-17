module

public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Hash
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Pre
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Test
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate

/-! ### `Dsa.RISCV64.PSearch.QPart`, which this module and modules that import it used -/

section

/-! # DSA parameter search on RISC-V: q

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/PX.lean`). `qPart` (`qPart_vp`):
the seed at `fSeed`, the tape's octets from `k`, copied before the block's
padding at `sMsg`, hashed into `sQ`, its top and low bits set (`shapeQ_vp`),
and tested with the tape from the cursor `u`. The claims after it: the
padding, and q's bytes at `sQ`.
-/

@[expose] public section

/-! ## DSA parameter search on RISC-V: `seed + offset + j`

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Add.lean` and `PHash.lean`'s
`seedAdd_vp`). The loop of `seedAdd` adds `a2` to the `a3` big-endian bytes
ending at `a0`, a byte at a time from the last, the carry and the addend's
higher bytes on in `a2` (`addLoop_ok`), against
`Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`). `SS.blk_bytes`: the block at `sMsg`
as a message and its padding.
-/

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- A `do … while (r ≠ 0)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `r` zero exactly when it is the last. -/
theorem loop_nz {body : Prog isa} {r : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr r != 0) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.nonzero r)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  obtain hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .nonzero r) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  obtain ev : isa.eval (.nonzero r) s' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero]; simpa using hz
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega, i + 1, by omega, rfl, hs'⟩

/-- The count after `addi r, r, -1` from `N - i`. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  rw [show N - i = (N - (i + 1)) + 1 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The count is nonzero exactly when it is not the last iteration. -/
theorem count_nz {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 (N - (i + 1)) != 0) = decide (i + 1 ≠ N) := by
  by_cases h : i + 1 = N
  · subst h; simp
  · have h1 : (BitVec.ofNat 64 (N - (i + 1))).toNat = N - (i + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have : BitVec.ofNat 64 (N - (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega
    rw [bne_iff_ne.mpr this]; simp [h]

/-- One step: the byte at `a0` := its sum with `a2`, `a2` := that sum's higher bits. -/
theorem addStep_ok {s : State} {a : Addr} (ha : s.gpr .a0 = a) (hw : InRegions s.wr a 1)
    (hc : (s.gpr .a2).toNat < 2 ^ 63) :
    WP isa (.block (addStep ++ ([.addi .a3 .a3 (-1)] : List Instr))) s fun t =>
      t.mem = s.mem.writeW a (BitVec.ofNat 8 ((s.mem a).toNat + (s.gpr .a2).toNat)) ∧
      t.gpr .a2 = BitVec.ofNat 64 (((s.mem a).toNat + (s.gpr .a2).toNat) / 256) ∧
      t.gpr .a0 = s.gpr .a0 - 1 ∧ t.gpr .a3 = s.gpr .a3 - 1 ∧
      Keep [.a0, .a1, .a2, .a3] s t ∧ t.sp = s.sp := by
  obtain hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [addStep, List.cons_append, List.nil_append]
  refine wp_lbu (by decide) (by rw [ha, BitVec.add_zero]) hr fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  obtain v : s₂.gpr .a1 = BitVec.ofNat 64 ((s.mem a).toNat + (s.gpr .a2).toNat) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .a2 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem a).isLt
    rw [Nat.mod_eq_of_lt (by omega : (s.mem a).toNat < 2 ^ 64)]
  refine wp_sb (a := a) (by decide)
    (by rw [u₂.other .a0 (by decide), u₁.other .a0 (by decide), ha, BitVec.add_zero])
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => ?_
  refine wp_srl (by decide) fun s₄ u₄ => ?_
  refine wp_subi (by decide) fun s₅ u₅ => ?_
  refine wp_subi (by decide) fun t u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃.mem, v, u₂.mem, u₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · have bl := (s.mem a).isLt
    rw [u₆.other .a2 (by decide), u₅.other .a2 (by decide), u₄.gpr, m₃.gpr, v]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  · rw [u₆.other .a0 (by decide), u₅.gpr, u₄.other .a0 (by decide), m₃.gpr, u₂.other .a0 (by decide),
      u₁.other .a0 (by decide)]; rfl
  · rw [u₆.gpr, u₅.other .a3 (by decide), u₄.other .a3 (by decide), m₃.gpr, u₂.other .a3 (by decide),
      u₁.other .a3 (by decide)]; rfl
  · refine ⟨fun r hr => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2, u₅.other _ hr.1, u₄.other _ hr.2.2.1, m₃.gpr, u₂.other _ hr.2.1,
      u₁.other _ hr.2.1]
  · rw [u₆.sp, u₅.sp, u₄.sp, m₃.sp, u₂.sp, u₁.sp]

/-- After `i` of the `n` bytes, with `c` carried. -/
structure AddInv (s₀ : State) (base : Addr) (n add i c : Nat) (t : State) : Prop where
  le : i ≤ n
  a0 : t.gpr .a0 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (n - 1)
  a2 : t.gpr .a2 = BitVec.ofNat 64 c
  cle : c ≤ add
  a3 : t.gpr .a3 = BitVec.ofNat 64 (n - i)
  frame : Frame [⟨base, n⟩] s₀.mem t.mem
  pre : ∀ j < n - i, t.mem (base + BitVec.ofNat 64 j) = s₀.mem (base + BitVec.ofNat 64 j)
  enc : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem base n) + add) =
    Spec.Dsa.encodeBE (n - i) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s₀.mem base n).take (n - i)) + c) ++
      Spec.Rsa.bytesAt t.mem (base + BitVec.ofNat 64 (n - i)) i
  keep : Keep [.a0, .a1, .a2, .a3] s₀ t
  sp : t.sp = s₀.sp

/-- One byte of the addition, from the last: `seedAdd_snoc` on a prefix of the bytes. -/
theorem encode_step (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) (c : Nat) :
    Spec.Dsa.encodeBE (k + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take (k + 1)) + c) =
      Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take k) +
        ((m (p + BitVec.ofNat 64 k)).toNat + c) / 256) ++
        [BitVec.ofNat 8 ((m (p + BitVec.ofNat 64 k)).toNat + c)] := by
  obtain e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Rsa.bytesAt]; exact hk)]
    simp [Spec.Rsa.bytesAt]
  obtain l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by simp [Spec.Rsa.bytesAt]; omega
  have := VG.Proof.Dsa.Generation.seedAdd_snoc ((Spec.Rsa.bytesAt m p n).take k) (m (p + BitVec.ofNat 64 k)) c
  rw [l] at this
  rw [e, this]

theorem bytesAt_cons (m : Mem) (p : Addr) (k i : Nat) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) (i + 1) =
      m (p + BitVec.ofNat 64 k) :: Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 (k + 1)) i := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show m (p + BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1)) = m (p + BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 j)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 3; omega

theorem addBody_ok {s₀ t : State} {base : Addr} {n add i c : Nat} (hn : n < 2048)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s₀.wr base n)
    (h : AddInv s₀ base n add i c t) (hi : i < n) :
    WP isa (.block (addStep ++ ([.addi .a3 .a3 (-1)] : List Instr))) t fun u =>
      AddInv s₀ base n add (i + 1) (((t.mem (base + BitVec.ofNat 64 (n - 1 - i))).toNat + c) / 256) u ∧
        (u.gpr .a3 != 0) = decide (i + 1 ≠ n) := by
  obtain hj : n - 1 - i < n := by omega
  obtain ea : t.gpr .a0 = base + BitVec.ofNat 64 (n - 1 - i) := by
    have e := h.a0
    rw [show n - 1 = (n - 1 - i) + i by omega, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 64 i) e
    simpa only [BitVec.add_sub_cancel] using this
  obtain hw1 : InRegions t.wr (base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.keep.2.2]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  obtain bl := (t.mem (base + BitVec.ofNat 64 (n - 1 - i))).isLt
  obtain c32 : c < 2 ^ 32 := by have := h.cle; omega
  refine WP.mono (addStep_ok ea hw1 (by rw [h.a2, BitVec.toNat_ofNat]; omega)) ?_
  rintro u ⟨mu, a2, a0, a3, Ku, spu⟩
  rw [h.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at mu a2
  refine ⟨⟨by omega, ?_, a2, ?_, ?_, ?_, ?_, ?_, (h.keep.trans Ku).mono (by simp), by rw [spu, h.sp]⟩, ?_⟩
  · rw [a0, ← h.a0, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (t.gpr .a0 - 1),
      BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]
    show t.gpr .a0 - 1 + 1 + _ = _
    rw [BitVec.sub_add_cancel]
  · have := h.cle; rcases Nat.eq_zero_or_pos c with rfl | hc0 <;> omega
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [a3, h.a3, e]
  · rw [mu]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · intro j hj'
    rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
      have := Offset.add_ofNat_ne base (a := j) (b := n - 1 - i) (by omega) (by omega) (by omega)
      exact this e)]
    exact h.pre j (by omega)
  · rw [h.enc, show n - i = (n - 1 - i) + 1 by omega, encode_step _ _ (by omega), ← h.pre (n - 1 - i) (by omega),
      show n - (i + 1) = n - 1 - i by omega, bytesAt_cons, List.append_assoc, List.singleton_append]
    congr 2
    · rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    · refine List.map_congr_left fun k hk => ?_
      obtain hk := List.mem_range.mp hk
      rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
        rw [Offset.add_add] at e
        exact Offset.add_ofNat_ne base (a := n - 1 - i + 1 + k) (b := n - 1 - i) (by omega) (by omega)
          (by omega) e)]
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [a3, h.a3, e]
    exact count_nz (by omega) (by omega)

/-- The loop of `seedAdd`: the `n` big-endian bytes at `base`, `a0` at their
last, plus `a2`, the count in `a3`. -/
theorem addLoop_ok {s : State} {base : Addr} {n add : Nat} (hn : 0 < n) (hn2 : n < 2048)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s.wr base n)
    (h0 : s.gpr .a0 = base + BitVec.ofNat 64 (n - 1)) (h2 : s.gpr .a2 = BitVec.ofNat 64 add)
    (h3 : s.gpr .a3 = BitVec.ofNat 64 n) :
    WP isa (Impl.Bignum.RISCV64.countLoop .a3 addStep) s fun t =>
      Spec.Rsa.bytesAt t.mem base n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem base n) + add) ∧
      Frame [⟨base, n⟩] s.mem t.mem ∧ Keep [.a0, .a1, .a2, .a3] s t ∧ t.sp = s.sp := by
  refine loop_nz (fun i t => ∃ c, AddInv s base n add i c t) hn
    (fun i hi t ⟨c, h⟩ => WP.mono (addBody_ok hn2 hfit hadd hw h hi) fun u ⟨hu, hz⟩ => ⟨⟨_, hu⟩, hz⟩)
    (fun t ⟨c, h⟩ => ?_) ⟨add, by omega, by rw [h0, BitVec.add_zero], h2, Nat.le_refl _, by rw [h3, Nat.sub_zero],
      Frame.refl _ _, fun _ _ => rfl, ?_, Keep.refl _ _, rfl⟩
  · rw [Nat.sub_zero, List.take_of_length_le (by simp [Spec.Rsa.bytesAt])]
    simp [Spec.Rsa.bytesAt]
  · have e := h.enc
    rw [Nat.sub_self, VG.Proof.Dsa.Generation.seedAdd_nil, List.nil_append, BitVec.add_zero] at e
    exact ⟨e.symm, h.frame, h.keep, h.sp⟩

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `seed + v` (big-endian, `seedlen` bytes). -/
abbrev seedPlus (G : GP) (sd : List Byte) (v : Nat) : List Byte := Spec.Dsa.encodeBE G.qLen (Spec.Dsa.decodeBE sd + v)

theorem GP.qLen_cases (G : GP) : G.qLen = 20 ∨ G.qLen = 32 := by
  simp only [GP.qLen, Spec.Dsa.generationQLen]; split <;> simp

/-- `offset + j` added to the seed at `sMsg`. -/
theorem seedAdd_vp {j off : Nat}
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2048) (hoff : off + j < 2 ^ 32)
    {sd : List Byte} (hsd : (sMsg, sd) ∈ c.cl) (hsl : sd.length = G.qLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (seedAdd G.qLen j)
      (St G { c with cl := (sMsg, seedPlus G sd (off + j)) :: cl' } X) := by
  unfold seedAdd
  have hq := G.qLen_cases
  obtain hq0 : 0 < G.qLen := by omega
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .a0 = G.sa (sMsg + G.qLen - 1) ∧
    s.gpr .a2 = BitVec.ofNat 64 (off + j) ∧ s.gpr .a3 = BitVec.ofNat 64 G.qLen
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block [scr .a0 (sMsg + G.qLen - 1), ld .a2 fOffset, .addi .a2 .a2 j, .li .a3 G.qLen]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · simp only [scr]
    refine wp_addi (by simp only [sMsg]; omega) fun s₁ u₁ => ?_
    obtain h₁ := h.of_upd u₁ (by decide)
    refine h₁.ldK (o := fOffset) (by decide) (by decide) ((h₁.gi.slotV hO).trans hOv) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine wp_addi hj fun s₃ u₃ => ?_
    obtain h₃ := h₂.of_upd u₃ (by decide)
    refine wp_li (by omega) fun t u => WP.block_nil ⟨⟨h₃.of_upd u (by decide), x⟩, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.gi.s6]
    · rw [u.other _ (by decide), u₃.gpr, u₂.gpr, BitVec.ofNat_add]
    · rw [u.gpr]
  refine VP.pub (G := G) (fun σ s ⟨⟨h, _⟩, _⟩ => ⟨h.gi.s6, by rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.a0, .a2, .a3]
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .a0, .a2, .a3])
      (Impl.Bignum.RISCV64.countLoop .a3 addStep), by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, a0, a2, a3⟩ ⟨_, b0, b2, b3⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a0, b0]
      · rw [a2, b2]
      · rw [a3, b3]) fun σ s ⟨⟨h, x⟩, r0, r2, r3⟩ => ?_
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have kb := gi.kBig
  have lens := gi.lens
  have hE : hEnd = 280 := rfl
  have nM : sMsg = 320 := rfl
  obtain hkB : sMsg + 64 ≤ kB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  obtain hw : InRegions s.wr (G.sa sMsg) G.qLen := gi.inScr (by omega) (by omega)
  refine (addLoop_ok (base := G.sa sMsg) hq0 (by omega) (by
      rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sMsg) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega) hoff hw (by rw [r0, GP.sa_add]; congr 2; omega) r2 r3).mono
    fun t ⟨e, f, K, sp⟩ => ⟨?_, x⟩
  obtain b := h.sb (sMsg, sd) hsd
  rw [hsl] at b
  rw [b] at e
  refine h.of_scrs K sp (os := [(sMsg, G.qLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Dsa.encodeBE_length]; exact e,
      by simp only [ClOk, VG.Proof.Dsa.encodeBE_length]; omega⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

/-- The block at `sMsg`: a message of `qLen` bytes and its padding. -/
theorem SS.blk_bytes {STK : Nat} {σ s : State} (h : SS G STK σ c s) {N : Nat} {md : MdStream.Md 64 N 8}
    {m : List Byte} (hm : (sMsg, m) ∈ c.cl) (hml : m.length = G.qLen)
    (hpad : (sMsg + G.qLen, padTail md G.qLen) ∈ c.cl) :
    Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk md m := by
  have hq := G.qLen_cases
  obtain b1 := h.sb _ hm
  obtain b2 := h.sb _ hpad
  obtain pl := padTail_length md (n := G.qLen) (by omega) rfl
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega, VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  obtain a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa (sMsg + G.qLen) := by
    rw [VG.Proof.Bignum.off, GP.sa_add, hml]
  rw [a]
  simp only at b2
  rw [b2]
  simp only [blk, padTail, hml, List.append_assoc]

end

end VG.Proof.Dsa.RISCV64.PSearch

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

/-- The seed at octet `k` of the tape. -/
abbrev seedAt (G : GP) (k : Nat) : List Byte := (G.randB.drop k).take G.qLen

/-- q's bytes, from the seed at `k`. -/
abbrev qBytes (G : GP) (k : Nat) : List Byte :=
  shapedOctets (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)) 7

/-- The claims after q: the padding, and q's bytes at `sQ`. -/
abbrev qClaims {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(sMsg + G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The key working space starts past the bytes below 8192. -/
theorem kB_ge (L : Nat) : 8192 ≤ kB L := by unfold kB pB; omega

theorem kB_le_wB (L : Nat) : kB L ≤ wB L := by unfold wB; omega

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

/-- The seed at `k`, in memory. -/
theorem GI.seedBytes (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.randLen) (hq0 : 0 < G.qLen) :
    Spec.Rsa.bytesAt s.mem (G.rand + BitVec.ofNat 64 k) G.qLen = seedAt G k := by
  obtain e := h.randBytes (u := k) (by omega)
  rw [GP.randP, ite_eq_right (by omega)] at e
  obtain ⟨d, hd⟩ : ∃ d, G.randLen - k = G.qLen + d := ⟨G.randLen - k - G.qLen, by omega⟩
  rw [hd, VG.Proof.Dsa.Generation.bytesAt_append] at e
  show _ = (G.randB.drop k).take G.qLen
  rw [← e, List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The seed at `k`, as a source of a copy. -/
theorem GI.seedSrc (h : GI G STK σ V LS s) {k : Nat} (hk : k + G.qLen ≤ G.randLen) (hq0 : 0 < G.qLen) :
    InRegions (s.rd ++ s.wr) (G.rand + BitVec.ofNat 64 k) G.qLen ∧
      (⟨G.rand + BitVec.ofNat 64 k, G.qLen⟩ : Region).Disjoint G.rScr := by
  have fit := h.randFit0
  obtain sub : Region.Sub ⟨G.rand + BitVec.ofNat 64 k, G.qLen⟩ G.rRand := Offset.sub_base _ hk
  obtain rC := h.pre.rC; rw [h.hG] at rC
  refine ⟨⟨G.rRand, ?_, Offset.contains_base _ hk (by omega)⟩, rC.sub_left sub⟩
  rw [h.rd, h.pre.rd, h.hG]; simp

end

/-! ## q's top and low bits -/

/-- The bit operations of the block. -/
abbrev shapeOps (N : Nat) : List Instr :=
  [.load .b .t2 .s6 sQ, .logicImm .or .t2 .t2 0x80, .store .b .t2 .s6 sQ,
    .load .b .t2 .s6 (sQ + N - 1), .logicImm .or .t2 .t2 1, .store .b .t2 .s6 (sQ + N - 1)]

theorem shape_cert {N : Nat} (hN : N = 20 ∨ N = 32) :
    ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6]) (.block (shapeOps N)) hc).isSome = true := by
  rcases hN with rfl | rfl
  · exact ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (shapeOps 20)), by kernel_rfl⟩
  · exact ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (shapeOps 32)), by kernel_rfl⟩

theorem or_byte (b : Byte) (v : Nat) :
    (b.setWidth 64 ||| BitVec.ofNat 64 v).setWidth 8 = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat]
  simp [hi, show i < 64 by omega]

/-- A byte write, at any address. -/
theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.writeW a v x = if (x - a).toNat < 1 then v else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i h
    rw [show (x - a).toNat = 0 by omega]
    simp
  · rfl

/-- A claim added after a step that kept a stage. -/
theorem SS.addCl {G : GP} {STK : Nat} {σ t : State} {c : Cfg} (h : SS G STK σ c t) {o : Nat} {bs : List Byte}
    (e : Spec.Rsa.bytesAt t.mem (G.sa o) bs.length = bs) (ok : ClOk G (o, bs)) :
    SS G STK σ { c with cl := (o, bs) :: c.cl } t :=
  ⟨h.gi, h.sb.cons e, fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ok
    · exact h.clOk y hy, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

section
variable {G : GP} {STK : Nat}

theorem shapeQ_vp {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : N = 20 ∨ N = 32)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sQ) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.t2] s t → t.sp = s.sp → Frame [G.rs sQ N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sQ) N = shapedOctets bs 7 → Q σ t) :
    VP P (.block (shapeOps N)) Q := by
  have hN2 : 2 ≤ N := by omega
  have hN' : N ≤ 32 := by omega
  refine VP.pub (SS.pub hF) [] (shape_cert hN) (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have k8 := kB_ge G.pLen
  have fit := gi.scrFit
  have nq : sQ = 512 := rfl
  have w : ∀ j < N, InRegions s.wr (G.sa (sQ + j)) 1 := fun j hj => gi.inScr (by omega)
  have r_of : ∀ j < N, InRegions (s.rd ++ s.wr) (G.sa (sQ + j)) 1 := fun j hj => gi.inRdWr (by omega)
  have a0 : s.gpr .s6 + BitVec.ofNat 64 sQ = G.sa sQ := by rw [gi.s6]
  have aN : s.gpr .s6 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [gi.s6, show sQ + N - 1 = sQ + (N - 1) by omega]
  refine WP.sp_eq ?_
  refine wp_lbu (by decide) a0 (by simpa using r_of 0 (by omega)) fun s₁ u₁ => ?_
  refine WP.wr (exec_logicImm (by decide)) fun s₂ u₂ => ?_
  refine wp_sb (a := G.sa sQ) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; simpa using w 0 (by omega)) fun s₃ m₃ => ?_
  have a3 : s₃.gpr .s6 + BitVec.ofNat 64 (sQ + N - 1) = G.sa (sQ + (N - 1)) := by
    rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact aN
  refine wp_lbu (by omega) a3
    (by rw [m₃.rd, m₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r_of _ (by omega)) fun s₄ u₄ => ?_
  refine WP.wr (exec_logicImm (by decide)) fun s₅ u₅ => ?_
  refine wp_sb (a := G.sa (sQ + (N - 1))) (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a3)
    (by rw [u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]; exact w _ (by omega)) fun t m₆ => WP.block_nil fun sp => ?_
  have K : Keep [.t2] s t := ⟨fun r hr => by
      have hr : r ≠ .t2 := by simpa using hr
      rw [m₆.gpr, u₅.other _ hr, u₄.other _ hr, m₃.gpr, u₂.other _ hr, u₁.other _ hr],
    by rw [m₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd], by rw [m₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
  have m₃' : s₃.mem = s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
    exact congrArg _ (or_byte _ 128)
  have b₃ : s₃.mem (G.sa (sQ + (N - 1))) = s.mem (G.sa (sQ + (N - 1))) := by
    rw [m₃', write1_apply, ite_eq_right_iff]
    intro hlt
    have e0 : G.sa (sQ + (N - 1)) - G.sa sQ = 0 :=
      BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
    exact absurd (show G.sa (sQ + (N - 1)) = G.sa sQ by
        rw [← BitVec.sub_add_cancel (G.sa (sQ + (N - 1))) (G.sa sQ), e0]; simp)
      (Offset.add_ofNat_ne G.scr (a := sQ + (N - 1)) (b := sQ) (by omega) (by omega) (by omega))
  have mt : t.mem = (s.mem.writeW (G.sa sQ) (s.mem (G.sa sQ) ||| 128#8)).writeW
      (G.sa sQ + BitVec.ofNat 64 (N - 1)) (s.mem (G.sa sQ + BitVec.ofNat 64 (N - 1)) ||| 1#8) := by
    rw [m₆.mem, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, b₃, ← m₃', GP.sa_add]
    exact congrArg _ (or_byte _ 1)
  have hb' := hb σ s hs
  have bl : bs.length = N := by rw [← hb']; simp [Spec.Rsa.bytesAt]
  refine k σ s t hs K sp ?_ ?_
  · rw [mt, GP.sa_add]
    have c0 : (G.rs sQ N).Contains (G.sa sQ) (8 / 8) :=
      Offset.contains G.scr (d := sQ) (n := 1) (e := sQ) (k := N) (Nat.le_refl _) (by omega) (by omega)
    have c1 : (G.rs sQ N).Contains (G.sa (sQ + (N - 1))) (8 / 8) :=
      Offset.contains G.scr (d := sQ + (N - 1)) (n := 1) (e := sQ) (k := N) (by omega) (by omega) (by omega)
    exact Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.writeW (r := G.rs sQ N) (w := 8) (Frame.refl _ _)
      List.mem_cons_self _ c0) List.mem_cons_self _ c1
  · rw [mt, ← bl]
    refine VG.Proof.Dsa.Generation.qShape_memory (by omega) (by omega) fun i hi => ?_
    rw [← hb']
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, bl ▸ hi]

end

/-! ## q -/

/-- The bounds of the bytes below 2048 that q uses, past the header and
before the key working space. -/
theorem q_bounds (G : GP) {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}
    (gi : GI G STK σ V LS s) : 2048 ≤ kB G.pLen ∧ kB G.pLen ≤ wB G.pLen ∧ 2048 + 256 * G.pLen ≤ G.scrLen * 8 := by
  have := gi.wBig; have := gi.kBig; have := kB_ge G.pLen
  exact ⟨by omega, by omega, by omega⟩

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- q from the seed at `k`, tested with the tape from `u`. -/
theorem qPart_vp {g : Geo} (HO : HashOk g.G) {L : Impl.Dsa.ProbablePrime.Layout} (ok : PrimeOk L g.qCode)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.randB.length = G.randLen)
    (hLb : L.bits = 8 * G.qLen) (hc0 : L.candidate = 0)
    (hsize : L.size ≤ 256 * G.pLen) (hL : ∀ r ∈ L.scratch, r.1 + r.2 ≤ 256 * G.pLen)
    {k u : Nat} (hk : k + G.qLen ≤ G.randLen) (hu : u ≤ G.randLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u)
    (hU' : ∀ o ∈ c.LS, fUsedOut + 8 ≤ o ∨ o + 8 ≤ fUsedOut) (hU88 : fUsedOut ∉ c.LS)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) :
    VP (St G c X) g.qPart
      (St G (testCfg c (qClaims HO.md G k) G.randLen
        (Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.randB.drop u))) X) := by
  have hqc2 := G.qLen_cases
  obtain hq0 : 0 < G.qLen := by omega
  obtain hq56 : G.qLen < 56 := by omega
  obtain pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md hq56 rfl
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hwl]; omega
  -- The hash and q.
  obtain hHl : (HO.H (seedAt G k)).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, hk4]
  obtain hne : HO.H (seedAt G k) ≠ [] := fun e => by rw [e] at hHl; simp at hHl; omega
  obtain qb : shapedOctets (HO.H (seedAt G k)) 7 = qBytes G k := by rw [hH]
  obtain qbl : (qBytes G k).length = G.qLen := by
    rw [← qb, shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHl]
  obtain hqc : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [← hH, hHl])
  rw [← hqc]
  have nM : sMsg = 320 := rfl
  have nS : sState = 384 := rfl
  have nC : sCS = 416 := rfl
  have nQ : sQ = 512 := rfl
  have nE : hEnd = 280 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  generalize hsd : seedAt G k = sd at hsl hHl hne qb
  let c1 : Cfg := { c with cl := [(sMsg, sd), (sMsg + G.qLen, pad)] }
  let c2 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, HO.H sd)] }
  let c3 : Cfg := { c with cl := [(sMsg + G.qLen, pad), (sQ, qBytes G k)] }
  unfold Geo.qPart
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  rw [hq, hp]
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ (VP.seq (G := St G c3 X) ?_ ?_))
  · -- The seed, before the padding.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega) (by decide) (by decide) (by decide)
      (P := G.rand + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by
        have := q_bounds G h.1.gi; simp only [ClOk, List.length_replicate]; omega)
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk hq0, hsd] at e
    obtain qB := q_bounds G h.gi
    refine (h'.addCl (o := sMsg) (bs := sd) (by rw [hsl]; exact e)
      (by simp only [ClOk, hsl]; omega)).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega⟩)
  · -- The hash.
    refine hash_vp HO (c := fun _ => c1) (fun σ s h => h.1) (msg := fun _ => sd) (dst := sQ)
      (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) (by decide) (by decide) fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes (md := HO.md) (by simp [c1]) hsl (by rw [hpd]; simp [c1])
    obtain qB := q_bounds G h.gi
    refine h.of_scrs K sp (os := [(sState, 32), (sCS, 80), (sQ, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate] <;> omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c1], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl] <;> omega
    · exact .inr ⟨by rw [hHl, ← hk4]; exact e, by simp only [ClOk, hHl]; omega⟩
  · -- q's shape.
    refine shapeQ_vp (c := fun _ => c2) (fun σ s h => h.1) (N := G.qLen) hqc2
      (bs := HO.H sd) (fun σ s ⟨h, _⟩ => by have := h.sb (sQ, HO.H sd) (by simp [c2]); rwa [hHl] at this)
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    obtain qB := q_bounds G h.gi
    refine h.of_scrs K sp (os := [(sQ, G.qLen)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [ClOk, List.length_replicate]; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; simp only [Apart, pl]; omega
    · exact .inr ⟨by rw [qbl, ← qb]; exact e, by simp only [ClOk, qbl]; omega⟩
  · -- The test.
    obtain hqs := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega) (seedAt G k)
    obtain hbl := VG.Proof.Dsa.Generation.qCandidate_bitLength (n := 8 * G.qLen) (by omega) (seedAt G k)
    rw [← hqc] at hqs hbl
    obtain hkq : sQ + G.qLen ≤ kB G.pLen := by have := kB_ge G.pLen; omega
    have := test_vp (X := X) (c := c3) (cb := qBytes G k) (src := sQ) (cl' := qClaims HO.md G k)
      (name := g.qName) ok hc0 hu hU hUv hwl hsize hL (by simp [c3]) (by rw [qbl]; exact hkq)
      (by rw [qbl, hLb]; omega) (by rw [qbl]; omega) (by rw [qbl]; omega) (by decide) hqs.1 (by rw [hbl, hLb])
      hU' hU88 fun y hy => ?_
    · rwa [qbl] at this
    obtain hw2 : 2048 ≤ wB G.pLen := by have := kB_ge G.pLen; have := kB_le_wB G.pLen; omega
    simp only [qClaims, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3, hpd], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, hpd, pl, qbl, decide_eq_true_eq]; omega
      · simp only [hpd, pl]; omega
    · refine ⟨List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨by simp [c3], ?_⟩), fun r _ => .inl ?_⟩
      · simp only [Apart, qbl, decide_eq_true_eq]; omega
      · simp only [qbl]; omega

end

end VG.Proof.Dsa.RISCV64.PSearch

end

end

-- separate module: X's hashes (`pX_vp`), which build beside p's arithmetic (`PArith`), both of which the search for p (`PPart`) imports

/-! # DSA parameter search on RISC-V: X

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/PHash.lean`, `PX.lean`). `pHash j`
(`pHash_vp`): the seed copied to `sMsg`, `offset + j` added to it
(`seedAdd_vp`, big-endian modulo `2^(8 seedlen)`), and its hash into its
place in X. `pHashes m` (`pHashes_vp`): the first `m` hashes of X, each just
below the one before, in one claim (`accB`) whose value is the sum of the
contributions (`accB_value`); `pX` (`pX_vp`): X's top bit set.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Ffdh.ParameterCandidate (topCut topByte)
open VG.Proof.Dsa.Generation (contributions pDigest)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The hash of the seed at `k` plus `off + j`, to its place in X. -/
theorem pHash_vp {g : Geo} (HO : HashOk g.G) {j : Nat}
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hj : j < 2048) (hoff : off + j < 2 ^ 32)
    (hd1 : sCS + 80 ≤ sX + G.pLen - (j + 1) * G.qLen) (hd2 : sX + G.pLen - (j + 1) * G.qLen + 32 ≤ 2048)
    (hpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ c.cl) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart sCS 80 x ∧
      Apart (sX + G.pLen - (j + 1) * G.qLen) G.qLen x) :
    VP (St G c X) (g.pHash j)
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX + G.pLen - (j + 1) * G.qLen,
        HO.H (seedPlus G (seedAt G k) (off + j))) :: cl' } X) := by
  have hqc2 := G.qLen_cases
  have hq0 : 0 < G.qLen := by omega
  have hq56 : G.qLen < 56 := by omega
  have pl := padTail_length HO.md hq56 rfl
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hwl]; omega
  have spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  have hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, hk4]
  have nM : sMsg = 320 := rfl
  have nS : sState = 384 := rfl
  have nC : sCS = 416 := rfl
  have nE : hEnd = 280 := rfl
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (sMsg + G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (sMsg + G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · -- The seed.
    refine copyIn_vp (c := fun _ => c) (fun σ s h => h.1) hq0 (by omega) (by decide) (by decide) (by decide)
      (P := G.rand + BitVec.ofNat 64 k) (fun σ s h => (h.1.gi.slotV hS).trans hSv)
      (fun σ s h => by have := q_bounds G h.1.gi; simp only [ClOk, List.length_replicate]; omega)
      (fun σ s h => h.1.gi.seedSrc hk hq0) fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
    rw [h.gi.seedBytes hk hq0] at e
    have qB := q_bounds G h.gi
    refine (h'.addCl (o := sMsg) (bs := seedAt G k) (by rw [hsl]; exact e)
      (by simp only [ClOk, hsl]; omega)).mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    refine List.mem_cons_of_mem _ (List.mem_filter.mpr ?_)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpad, by simp only [Apart, decide_eq_true_eq]; omega⟩
    · obtain ⟨m, a, -⟩ := hcl y hy
      exact ⟨m, by simp only [Apart, decide_eq_true_eq] at a ⊢; omega⟩
  · -- `offset + j`.
    exact seedAdd_vp (c := c1) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by omega)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart] at a ⊢; omega⟩
  · -- The hash.
    refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) hd1 hd2
      fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
    · exact h.blk_bytes (md := HO.md) (by simp [c2]) spl (by rw [hpd]; simp [c2])
    have qB := q_bounds G h.gi
    refine h.of_scrs K sp (os := [(sState, 32), (sCS, 80), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)])
      (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ hr) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [ClOk, List.length_replicate, hk4] <;> omega
    rcases List.mem_cons.mp hy with rfl | hy
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, hk4] <;> omega
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hk4] at e
      exact .inr ⟨by rw [hHl]; exact e, by simp only [ClOk, hHl]; omega⟩
    · obtain ⟨m, a, b, d, d'⟩ := hcl y hy
      refine .inl ⟨by simp [c2, hy], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, hk4] at a b d d' ⊢ <;> omega

end

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- A slice of bytes. -/
theorem bytesAt_slice' (m : Mem) (p : Addr) {k n len : Nat} (h : k + n ≤ len) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) n = ((Spec.Rsa.bytesAt m p len).drop k).take n := by
  obtain ⟨r, rfl⟩ : ∃ r, len = k + (n + r) := ⟨len - k - n, by omega⟩
  rw [VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

/-- A piece of a stage, proven for the three widths: no other state is in
it. -/
theorem VP.byLens {G : GP} {c : Cfg} {X : State → Prop} {p : Prog isa} {Q : State → State → Prop}
    (h : (G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) → VP (St G c X) p Q) : VP (St G c X) p Q := by
  by_cases e : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  · exact h e
  · exact VP.of_false fun σ s hs => e hs.1.lens

/-- `(L − 1) / N`, the number of whole hashes below X's top one. -/
abbrev cnt (G : GP) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

/-- The bounds of X, for each width. -/
theorem cnt_facts (G : GP) (h : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    (cnt G + 1) * G.qLen ≤ G.pLen + 64 ∧ G.pLen ≤ (cnt G + 1) * G.qLen ∧ cnt G + 1 < 2048 ∧
      G.pLen ≤ 384 := by
  rcases h with e | e | e <;> simp only [cnt, GP.qLen, e] <;> decide

section
variable {G : GP} {Gh : Hash}

/-- Hash `j` of X, from the seed at `k` and the offset `off`. -/
abbrev hX (HO : HashOk Gh) (G : GP) (k off j : Nat) : List Byte := HO.H (seedPlus G (seedAt G k) (off + j))

/-- The first `m` hashes of X, the last first. -/
def accB (HO : HashOk Gh) (G : GP) (k off : Nat) : Nat → List Byte
  | 0 => []
  | m + 1 => hX HO G k off m ++ accB HO G k off m

/-- Where the first `m` hashes of X start. -/
abbrev pStart (G : GP) (m : Nat) : Nat := sX + G.pLen - m * G.qLen

theorem accB_length (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen) :
    ∀ m, (accB HO G k off m).length = m * G.qLen
  | 0 => by simp [accB]
  | m + 1 => by rw [accB, List.length_append, hl, accB_length HO hl m, Nat.succ_mul]; omega

theorem accB_value (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen) :
    ∀ m, Spec.Dsa.decodeBE (accB HO G k off m) = contributions (8 * G.qLen) (pDigest (8 * G.qLen) (seedAt G k) off) m
  | 0 => rfl
  | m + 1 => by
    rw [accB, VG.Proof.Dsa.Generation.prepend_digest, accB_value HO hl hH hsl m,
      VG.Proof.Dsa.Generation.contributions_succ, accB_length HO hl m]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (m * G.qLen) = m * (8 * G.qLen) by
      rw [Nat.mul_left_comm]]
    congr 1
    simp only [hX, hH, pDigest, seedPlus, hsl, Nat.add_assoc]

/-- Other claims, which the memory holds. -/
theorem SS.reclaim {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {cl' : Claims}
    (hcl : ∀ x ∈ cl', Spec.Rsa.bytesAt s.mem (G.sa x.1) x.2.length = x.2 ∧ ClOk G x) :
    SS G STK σ { c with cl := cl' } s :=
  ⟨h.gi, fun x hx => (hcl x hx).1, fun x hx => (hcl x hx).2, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

/-- Two claims side by side, as one. -/
theorem SB.join {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {a b : List Byte} (ha : (o, a) ∈ cl)
    (hb : (o + a.length, b) ∈ cl) : Spec.Rsa.bytesAt m (G.sa o) (a ++ b).length = a ++ b := by
  rw [List.length_append, VG.Proof.Dsa.Generation.bytesAt_append, h _ ha]
  have e : VG.Proof.Bignum.off (G.sa o) a.length = G.sa (o + a.length) := by
    rw [VG.Proof.Bignum.off, GP.sa_add]
  rw [e, h _ hb]

/-- The claims during X. -/
abbrev pCfg (c : Cfg) (HO : HashOk Gh) (G : GP) (k off m : Nat) (rest : Claims) : Cfg :=
  { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (pStart G m, accB HO G k off m) :: rest }

/-- The first `m` hashes of X. -/
theorem pHashes_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    {k off n : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hn : n < 2048) (hoff : off + n < 2 ^ 32)
    (hnq : n * G.qLen ≤ G.pLen + 64) (hp384 : G.pLen ≤ 384) {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart sCS 80 x ∧
      Apart (pStart G n) (n * G.qLen) x) :
    ∀ m ≤ n, VP (St G (pCfg c HO G k off 0 rest) X) (g.pHashes m) (St G (pCfg c HO G k off m rest) X)
  | 0, _ => VP.block_nil fun _ _ h => h
  | m + 1, hm => by
    have ih := pHashes_vp (X := X) HO hp hq hk4 hwl hk hS hSv hO hOv hn hoff hnq hp384 hrest m (by omega)
    refine VP.seq ih ?_
    have hqc2 := G.qLen_cases
    have nX : sX = 576 := rfl
    have nS : sState = 384 := rfl
    have nC : sCS = 416 := rfl
    have nM : sMsg = 320 := rfl
    have nE : hEnd = 280 := rfl
    have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
      rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, hk4]
    have al := accB_length HO hHl m
    have hm1 : (m + 1) * G.qLen = m * G.qLen + G.qLen := Nat.succ_mul _ _
    have hmn : (m + 1) * G.qLen ≤ n * G.qLen := Nat.mul_le_mul_right _ hm
    have e1 : pStart G (m + 1) + G.qLen = pStart G m := by
      simp only [pStart]; omega
    refine (pHash_vp (c := pCfg c HO G k off m rest) (j := m) HO hp hq hk4 hwl hk hS hSv hO hOv (by omega)
      (by omega) (by omega) (by omega) (by simp) (cl' := (pStart G m, accB HO G k off m) :: rest)
      fun x hx => ?_).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.reclaim fun y hy => ?_, x⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp only [Apart, al, pStart] <;> omega
      · obtain ⟨a, b, d, d'⟩ := hrest x hx
        refine ⟨by simp [hx], a, b, d, ?_⟩
        simp only [Apart, pStart] at d' ⊢
        omega
    · have sb := h.sb
      have cl := h.clOk
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact ⟨sb _ (by simp), cl _ (by simp)⟩
      · have j := sb.join (o := pStart G (m + 1)) (a := hX HO G k off m) (b := accB HO G k off m)
          (by simp [pStart]) (by rw [hHl, e1]; simp)
        refine ⟨j, ?_⟩
        have qB := q_bounds G h.gi
        show ClOk G (pStart G (m + 1), hX HO G k off m ++ accB HO G k off m)
        rw [ClOk, List.length_append, hHl, accB_length HO hHl]
        simp only [pStart]; omega
      · exact ⟨sb _ (by simp [hy]), cl _ (by simp [hy])⟩

theorem top_memory {m : Mem} {op : Addr} {n : Nat} (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW op (m op ||| 128#8)) op n = topCut (Spec.Rsa.bytesAt m op n) 7 := by
  have hne : Spec.Rsa.bytesAt m op n ≠ [] := by
    intro h; have := bytesAt_length' m op n; rw [h] at this; simp at this; omega
  apply List.ext_getElem
  · rw [bytesAt_length', VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, bytesAt_length']
  · intro i hi hi'
    have hil : i < n := by simpa only [bytesAt_length'] using hi
    have hget : (topCut (Spec.Rsa.bytesAt m op n) 7)[i] = (topCut (Spec.Rsa.bytesAt m op n) 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, VG.Proof.Ffdh.ParameterCandidate.topCut_getD, VG.Proof.Dsa.Generation.topByte_seven]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeW8_apply]
    by_cases hiz : i = 0
    · subst i; simp [show 0 < n by omega]
    · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
        simpa using Offset.add_ofNat_ne op (by omega : i < 2 ^ 64) (by decide : 0 < 2 ^ 64) hiz
      simp [hiz, hne0, hil]

/-- The block that sets X's top bit. -/
abbrev topOps : List Instr := [.load .b .t2 .s6 sX, .logicImm .or .t2 .t2 0x80, .store .b .t2 .s6 sX]

/-- X's top bit set. -/
theorem topX_vp {STK : Nat} {P Q : State → State → Prop} {c : State → Cfg} {N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s) (hN : 1 ≤ N) (hN' : sX + N ≤ kB G.pLen)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sX) N = bs)
    (k : ∀ σ s t, P σ s → Keep [.t2] s t → t.sp = s.sp → Frame [G.rs sX N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sX) N = topCut bs 7 → Q σ t) :
    VP P (.block topOps) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block topOps), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.wBig
  have fit := gi.scrFit
  have kb := kB_le_wB G.pLen
  have p1 : 0 < G.pLen := by rcases gi.lens with e | e | e <;> omega
  have nX : sX = 576 := rfl
  have c0 : (G.rs sX N).Contains (G.sa sX) (8 / 8) :=
    Offset.contains G.scr (d := sX) (n := 1) (e := sX) (k := N) (Nat.le_refl _) (by omega) (by omega)
  have a0 : s.gpr .s6 + BitVec.ofNat 64 sX = G.sa sX := by rw [gi.s6]
  refine WP.sp_eq ?_
  refine wp_lbu (by decide) a0 (gi.inRdWr (by omega)) fun s₁ u₁ => ?_
  refine WP.wr (exec_logicImm (by decide)) fun s₂ u₂ => ?_
  refine wp_sb (a := G.sa sX) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a0)
    (by rw [u₂.wr, u₁.wr]; exact gi.inScr (by omega)) fun t m₃ => WP.block_nil fun sp => ?_
  have K : Keep [.t2] s t := ⟨fun r hr => by
      have hr : r ≠ .t2 := by simpa using hr
      rw [m₃.gpr, u₂.other _ hr, u₁.other _ hr], by rw [m₃.rd, u₂.rd, u₁.rd], by rw [m₃.wr, u₂.wr, u₁.wr]⟩
  have mt : t.mem = s.mem.writeW (G.sa sX) (s.mem (G.sa sX) ||| 128#8) := by
    rw [m₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
    exact congrArg _ (or_byte _ 128)
  refine k σ s t hs K sp ?_ ?_
  · rw [mt]
    exact Frame.writeW (r := G.rs sX N) (w := 8) (Frame.refl _ _) List.mem_cons_self _ c0
  · rw [mt, top_memory hN (by omega), hb σ s hs]

/-- X's bytes: the low `pLen` bytes of the hashes, the top bit set. -/
abbrev xBytes (HO : HashOk Gh) (G : GP) (k off : Nat) : List Byte :=
  topCut ((accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen)) 7

theorem decodeBE_drop (bs : List Byte) (d : Nat) :
    Spec.Dsa.decodeBE (bs.drop d) = Spec.Dsa.decodeBE bs % 256 ^ (bs.length - d) := by
  have e := VG.Proof.Dsa.decodeBE_append (bs.take d) (bs.drop d)
  rw [List.take_append_drop, List.length_drop] at e
  rw [e, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := VG.Proof.Dsa.decodeBE_lt (bs.drop d); rwa [List.length_drop] at this)]

/-- X's value. -/
theorem xBytes_value {A : List Byte} {d n : Nat} (hA : A.length = d + n) (hn : 1 ≤ n) :
    Spec.Dsa.decodeBE (topCut (A.drop d) 7) = Spec.Dsa.decodeBE A % 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
  have hne : A.drop d ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop] at this; simp at this; omega
  rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.topCut_value hne (by decide),
    ← VG.Proof.Dsa.decodeBE_os2ip, decodeBE_drop, List.length_drop, hA,
    show d + n - d = n by omega, show 8 * (n - 1) + 7 = 8 * n - 1 by omega,
    show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul],
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- The candidate p of the spec, from X's value. -/
theorem pCandidate_xBytes (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hp1 : 1 ≤ G.pLen) (hc : G.pLen ≤ (cnt G + 1) * G.qLen) (q : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) q (seedAt G k) off =
      Spec.Dsa.decodeBE (xBytes HO G k off) + 1 - Spec.Dsa.decodeBE (xBytes HO G k off) % (2 * q) := by
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega) hlen,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega),
    VG.Proof.Dsa.Generation.pReduction_orOne, xBytes,
    xBytes_value (by rw [accB_length HO hl]; omega) hp1, accB_value HO hl hH hsl]

/-- X, from the seed at `k` and the offset `off`, at `sX`. -/
theorem pX_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hwl : G.randB.length = G.randLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.randLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.rand + BitVec.ofNat 64 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 64 off) (hoff : off + (cnt G + 1) < 2 ^ 32)
    {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart sMsg 64 x ∧ Apart sState 32 x ∧ Apart sCS 80 x ∧
      Apart (pStart G (cnt G + 1)) ((cnt G + 1) * G.qLen) x) :
    VP (St G (pCfg c HO G k off 0 rest) X) g.pX
      (St G { c with cl := (sMsg + G.qLen, padTail HO.md G.qLen) :: (sX, xBytes HO G k off) :: rest } X) := by
  refine VP.byLens fun hlens => ?_
  have hc := cnt_facts G hlens
  have hqc2 := G.qLen_cases
  have hcount : g.count = cnt G := by simp only [Geo.count, hp, hq]
  have nX : sX = 576 := rfl
  have nE : hEnd = 280 := rfl
  have nM : sMsg = 320 := rfl
  have hq56 : G.qLen < 56 := by omega
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, hk4]
  have al := accB_length HO hHl (cnt G + 1)
  have hd : pStart G (cnt G + 1) + ((cnt G + 1) * G.qLen - G.pLen) = sX := by simp only [pStart]; omega
  have k8 := kB_ge G.pLen
  unfold Geo.pX
  rw [hcount]
  refine VP.seq (pHashes_vp HO hp hq hk4 hwl hk hS hSv hO hOv hc.2.2.1 (by omega) hc.1 hc.2.2.2 hrest _
    (Nat.le_refl _)) ?_
  refine topX_vp (c := fun _ => pCfg c HO G k off (cnt G + 1) rest) (fun σ s h => h.1) (N := G.pLen)
    (by omega) (by omega) (bs := (accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen))
    (fun σ s ⟨h, _⟩ => ?_) fun σ s t ⟨h, x⟩ K sp f e => ⟨?_, x⟩
  · have b := h.sb (pStart G (cnt G + 1), accB HO G k off (cnt G + 1)) (by simp)
    simp only at b
    rw [al] at b
    have a : G.sa sX = G.sa (pStart G (cnt G + 1)) + BitVec.ofNat 64 ((cnt G + 1) * G.qLen - G.pLen) := by
      rw [GP.sa_add, hd]
    rw [a, bytesAt_slice' _ _ (len := (cnt G + 1) * G.qLen) (by omega), b, List.take_of_length_le (by
      rw [List.length_drop, al]; omega)]
  have qB := q_bounds G h.gi
  refine h.of_scrs K sp (os := [(sX, G.pLen)]) (fun p hp => ?_) (f.mono fun r hr => List.mem_append_left _ (by
    simpa [GP.rss] using hr)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · refine .inl ⟨by simp, fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, padTail_length HO.md (show G.qLen < 56 by omega) rfl]; omega
  rcases List.mem_cons.mp hy with rfl | hy
  · have hl : (xBytes HO G k off).length = G.pLen := by
      rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
        rw [← List.length_pos_iff, List.length_drop, al]; omega), List.length_drop, al]; omega
    exact .inr ⟨by rw [hl]; exact e, by simp only [ClOk, hl]; omega⟩
  · obtain ⟨_, _, _, d⟩ := hrest y hy
    refine .inl ⟨by simp [hy], fun p hp => ?_⟩
    simp only [List.mem_singleton] at hp; subst hp
    simp only [Apart, pStart] at d ⊢; omega

end

end VG.Proof.Dsa.RISCV64.PSearch
