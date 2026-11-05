module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Hash
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Pre
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: `seed + offset + j`

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Add.lean` and `PHash.lean`'s
`seedAdd_vp`). The loop of `seedAdd` adds `a2` to the `a3` big-endian bytes
ending at `a0`, a byte at a time from the last, the carry and the addend's
higher bytes on in `a2` (`addLoop_ok`), against
`Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`). `SS.blk_bytes`: the block at `sMsg`
as a message and its padding.
-/

@[expose] public section

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
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .nonzero r) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.nonzero r) s' = some (decide (i + 1 ≠ N)) := by
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
  have hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [addStep, List.cons_append, List.nil_append]
  refine wp_lbu (by decide) (by rw [ha, BitVec.add_zero]) hr fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  have v : s₂.gpr .a1 = BitVec.ofNat 64 ((s.mem a).toNat + (s.gpr .a2).toNat) := by
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
  have e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Rsa.bytesAt]; exact hk)]
    simp [Spec.Rsa.bytesAt]
  have l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by simp [Spec.Rsa.bytesAt]; omega
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
  have hj : n - 1 - i < n := by omega
  have ea : t.gpr .a0 = base + BitVec.ofNat 64 (n - 1 - i) := by
    have e := h.a0
    rw [show n - 1 = (n - 1 - i) + i by omega, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 64 i) e
    simpa only [BitVec.add_sub_cancel] using this
  have hw1 : InRegions t.wr (base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.keep.2.2]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  have bl := (t.mem (base + BitVec.ofNat 64 (n - 1 - i))).isLt
  have c32 : c < 2 ^ 32 := by have := h.cle; omega
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
      have hk := List.mem_range.mp hk
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
  have hq0 : 0 < G.qLen := by omega
  let M : State → State → Prop := fun σ s => St G c X σ s ∧ s.gpr .a0 = G.sa (sMsg + G.qLen - 1) ∧
    s.gpr .a2 = BitVec.ofNat 64 (off + j) ∧ s.gpr .a3 = BitVec.ofNat 64 G.qLen
  refine VP.seq (G := M) (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block [scr .a0 (sMsg + G.qLen - 1), ld .a2 fOffset, .addi .a2 .a2 j, .li .a3 G.qLen]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · simp only [scr]
    refine wp_addi (by simp only [sMsg]; omega) fun s₁ u₁ => ?_
    have h₁ := h.of_upd u₁ (by decide)
    refine h₁.ldK (o := fOffset) (by decide) (by decide) ((h₁.gi.slotV hO).trans hOv) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine wp_addi hj fun s₃ u₃ => ?_
    have h₃ := h₂.of_upd u₃ (by decide)
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
  have hkB : sMsg + 64 ≤ kB G.pLen := by rcases lens with e | e | e <;> rw [e] <;> decide
  have hw : InRegions s.wr (G.sa sMsg) G.qLen := gi.inScr (by omega) (by omega)
  refine (addLoop_ok (base := G.sa sMsg) hq0 (by omega) (by
      rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sMsg) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega) hoff hw (by rw [r0, GP.sa_add]; congr 2; omega) r2 r3).mono
    fun t ⟨e, f, K, sp⟩ => ⟨?_, x⟩
  have b := h.sb (sMsg, sd) hsd
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
  have b1 := h.sb _ hm
  have b2 := h.sb _ hpad
  have pl := padTail_length md (n := G.qLen) (by omega) rfl
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega, VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  have a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa (sMsg + G.qLen) := by
    rw [VG.Proof.Bignum.off, GP.sa_add, hml]
  rw [a]
  simp only at b2
  rw [b2]
  simp only [blk, padTail, hml, List.append_assoc]

end

end VG.Proof.Dsa.RISCV64.PSearch
