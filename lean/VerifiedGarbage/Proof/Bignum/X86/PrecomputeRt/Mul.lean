module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn

/-! # The six squares of the precomputation at a run-time width

`mul 4 4 4 5` (`PublicRt.mul`, `ws_len` from argument 5) squares number 4
by a call of `vg_rsa_mont_mul_at` (`sq_ok`, from `RtCall.call_ok`); six of
them take `x R` for `x = 2^W` to `x^64 R = R²` modulo `M` (`squares_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (argAt_alloc mulBody_noSp mulArgs_ok mulArg mulFrame_val32 mulFrame_hdr numAt
  wb nw wb_eq wb_le countLoop count1_zf)
open VG.Proof.Rsa.MontMul (scratchBytes)

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- `PcIn` across changes to the working space and the stack below `esp`. -/
theorem PcIn.keepF (h : PcIn base bytes len args s) {regs : List Reg} (K : Keeps regs s t) (di : .edi ∉ regs)
    (sp : .esp ∉ regs) (R : CallRoom (s.gpr .esp) base bytes) (top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    (F : Frame [⟨base, bytes⟩, below (s.gpr .esp) 96] s.mem t.mem) : PcIn base bytes len args t := by
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space, fun i hi => ?_, h.wLen, h.nLen,
    h.hbase, h.hbytes, h.outFit, h.nFit, by rw [K.2.2]; exact h.outWrite, by rw [K.2.1, K.2.2]; exact h.nRead,
    h.outApart, h.nApart, by simp only [argAddr, esp]; exact h.outArgs⟩
  have A := h.stack i hi
  refine ⟨A.stack.keep K sp, ?_⟩
  rw [← A.value]
  unfold VG.Proof.Dsa.X86.stackValue
  rw [show VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i by
    simp only [VG.Proof.Dsa.X86.stackAddress, esp]]
  refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.stack.apart
  · have low := R.low
    have ea : (VG.Proof.Dsa.X86.stackAddress s i).toNat = (s.gpr .esp).toNat + (4 + 4 * i) := by
      simp only [VG.Proof.Dsa.X86.stackAddress, addr, PublicRt.setWidth_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have eb : ((s.gpr .esp - BitVec.ofNat 32 96).setWidth 64).toNat = (s.gpr .esp).toNat - 96 := by
      rw [PublicRt.setWidth_toNat, sub_toNat (by omega)]
    exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 96) (.inl (by dsimp only; rw [eb, ea]; omega))
      (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; omega)).symm

/-- The callee's offsets for the square of number 4. -/
theorem PcIn.offs (h : PcIn base bytes len args s) :
    Offs bytes (Spec.Rsa.modulusWords len) numOff invOff (numAt len 5) (numAt len 4) (numAt len 4)
      (numAt len 4) := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have := h.dimensions
  refine ⟨this.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [numAt, numOff, wb, invOff, scratchBytes, VG.Proof.Rsa.MontMul.Apart] at * <;> omega

end

theorem mulArg_eq (len : Nat) (edi wl : BitVec 32) (i : Nat) :
    mulArg len 4 4 4 edi wl i = callArg edi wl (Spec.Rsa.modulusWords len) numOff invOff (numAt len 5)
      (numAt len 4) (numAt len 4) (numAt len 4) i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> rfl

theorem sq_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) (R : CallRoom (s.gpr .esp) base bytes)
    (hinv : (val32 s.mem base numOff (nw len) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (numAt len 4) (nw len) < val32 s.mem base numOff (nw len)) :
    WP isa (PublicRt.mul 4 4 4 5) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (numAt len 4), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below (s.gpr .esp) 96]
        s.mem t.mem ∧
      val32 t.mem base (numAt len 4) (nw len) < val32 s.mem base numOff (nw len) ∧
      val32 t.mem base (numAt len 4) (nw len) * 2 ^ (32 * nw len) % val32 s.mem base numOff (nw len) =
        val32 s.mem base (numAt len 4) (nw len) * val32 s.mem base (numAt len 4) (nw len) %
          val32 s.mem base numOff (nw len) := by
  have low := R.low
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have C := call_ok (is := mulArgs 4 4 4 5) h.scratch h.hbytes R h.offs hinv hB (mulBody_noSp 4 4 4 5) (by
    refine WP.mono (mulArgs_ok (f := allocFrame 36 s) (len := len) (o := 4) (a := 4) (b := 4) (wl := 5)
      (argAt_alloc h.width) (argAt_alloc (h.stack 5 (by decide)).readSrc) h.upper (by omega) (by omega)
      (by omega) (by rw [fEsp, VG.X86.sub_toNat (by omega)]; omega)
      (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)) fun g ⟨K, F, Rg⟩ => ⟨K, F, fun i hi => ?_⟩
    rw [Rg i hi, mulArg_eq, allocFrame_gpr _ _ (by decide)])
  refine WP.mono C fun t ⟨cs, rd, wr, F, L, V⟩ => ⟨cs, rd, wr, ?_, L, ?_⟩
  · rwa [show scratchBytes (Spec.Rsa.modulusWords len) = 3 * wb len + 56 by simp only [scratchBytes, wb]; omega] at F
  · rwa [show 64 * Spec.Rsa.modulusWords len = 32 * nw len by simp only [nw]; omega] at V

/-- What the squares keep: the inputs, the room below `esp`, the modulus `M` and its inverse, number 4 below
`M` in Montgomery form `x R`, and `esi` counting down. -/
structure SqInv (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (M x n : Nat) (t : State) :
    Prop where
  pi : PcIn base bytes len args t
  keep : Keeps [.eax, .ecx, .edx, .esi] s t
  frame : Frame [⟨off base (numAt len 4), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩,
    below (s.gpr .esp) 96] s.mem t.mem
  mod : val32 t.mem base numOff (nw len) = M
  inv : (M * w32 t.mem base invOff + 1) % 2 ^ 32 = 0
  lt : val32 t.mem base (numAt len 4) (nw len) < M
  val : val32 t.mem base (numAt len 4) (nw len) % M = x * 2 ^ (32 * nw len) % M
  esi : (t.gpr .esi).toNat = n

theorem squares_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) (R : CallRoom (s.gpr .esp) base bytes) (top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    {M : Nat} (hM : val32 s.mem base numOff (nw len) = M) (hinv : (M * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (numAt len 4) (nw len) < M)
    (hX : val32 s.mem base (numAt len 4) (nw len) % M = 2 ^ Spec.Rsa.modulusWords len * 2 ^ (32 * nw len) % M) :
    WP isa PrecomputeFn.squares s fun t =>
      val32 t.mem base (numAt len 4) (nw len) = 2 ^ (128 * Spec.Rsa.modulusWords len) % M ∧
      Frame [⟨off base (numAt len 4), wb len⟩, ⟨off base (numAt len 5), 3 * wb len + 56⟩, below (s.gpr .esp) 96]
        s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .esi] s t := by
  have nw' := h.scratch.nowrap
  have f5 := (h.fits (j := 5) (by decide)).2
  have f4 := (h.fits (j := 4) (by decide)).1
  have f0 := (h.fits (j := 0) (by decide)).1
  have wbe := wb_eq len
  have cop : ∀ k, Nat.Coprime (2 ^ k) M := fun k => by
    have hmod : (M * w32 s.mem base invOff + 1) % 2 = 0 := by omega
    refine VG.Proof.Bignum.coprime_pow2 ?_ k
    rcases Nat.mod_two_eq_zero_or_one M with hm | hm
    · rw [Nat.add_mod, Nat.mul_mod, hm] at hmod; simp at hmod
    · exact hm
  unfold PrecomputeFn.squares
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => WP.block_nil ?_)
  have K₀ : Keeps [.esi] s s₀ := u₀.keeps
  let x : Nat → Nat := fun j => 2 ^ (Spec.Rsa.modulusWords len * 2 ^ j)
  have I₀ : SqInv s base bytes len args M (x 0) 6 s₀ := by
    refine ⟨h.keep K₀ (by decide) (by decide) (by rw [u₀.mem]; exact Outside.refl _ _ _ _), K₀.mono (by decide),
      by rw [u₀.mem]; exact Frame.refl _ _, by rw [u₀.mem]; exact hM, by rw [u₀.mem]; exact hinv,
      by rw [u₀.mem]; exact hB, by rw [u₀.mem, hX]; simp only [x, Nat.pow_zero, Nat.mul_one], by rw [u₀.gpr]; rfl⟩
  have fin : ∀ t, SqInv s base bytes len args M (x 6) (6 - 6) t →
      val32 t.mem base (numAt len 4) (nw len) = 2 ^ (128 * Spec.Rsa.modulusWords len) % M := fun t I => by
    have V := I.val
    rw [Nat.mod_eq_of_lt I.lt] at V
    rw [V]
    congr 1
    simp only [x, nw, ← Nat.pow_add]
    congr 1
    omega
  refine WP.mono (countLoop (N := 6) (by decide) (fun j t => SqInv s base bytes len args M (x j) (6 - j) t) ?_ I₀)
    fun t I => ⟨fin t I, I.frame, I.keep⟩
  rintro j t hj I
  have sp : t.gpr .esp = s.gpr .esp := I.keep.1 _ (by decide)
  have Rt : CallRoom (t.gpr .esp) base bytes := by rw [sp]; exact R
  refine WP.seq (WP.mono (sq_ok I.pi Rt (by rw [I.mod]; exact I.inv) (by rw [I.mod]; exact I.lt))
    fun u ⟨cs, rd, wr, F, L, V⟩ => ?_)
  have Ku : Keeps [.eax, .ecx, .edx] t u :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [calleeSaved]), rd, wr⟩
  rw [sp] at F
  have Mu : val32 u.mem base numOff (nw len) = M := by
    rw [← I.mod, show numOff = numAt len 0 by simp [numAt]]
    exact mulFrame_val32 R nw' F (.inl (by simp only [numAt]; omega)) (by simp only [numAt]; omega)
      (by simp only [numAt] at f0 ⊢; omega) f4 f5
  have Iu : w32 u.mem base invOff = w32 t.mem base invOff := by
    unfold w32
    simp only [Mem.readW]
    rw [mulFrame_hdr R nw' F (d := invOff) (k := 4) (by decide) (by simp only [numAt, numOff, invOff] at f0 ⊢; omega)
      f4 f5]
  rw [I.mod] at L V
  refine wp_subZ rfl fun v e z => WP.block_nil ?_
  have Fs : Frame [⟨base, bytes⟩, below (s.gpr .esp) 96] t.mem u.mem := F.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have piu := I.pi.keepF Ku (by decide) (by decide) Rt (by rw [sp]; exact top) (by rw [sp]; exact Fs)
  obtain ⟨c₁, c₂⟩ := count1_zf (N := 6) (x := t.gpr .esi) (by rw [I.esi]) hj
  have esiu : u.gpr .esi = t.gpr .esi := Ku.1 _ (by decide)
  refine ⟨⟨piu.keep e.keeps (by decide) (by decide) (by rw [e.mem]; exact Outside.refl _ _ _ _),
    ((I.keep.trans (Ku.mono (by decide))).trans (e.keeps.mono (by decide))), ?_, by rw [e.mem, Mu],
    by rw [e.mem, Iu]; exact I.inv, by rw [e.mem]; exact L, ?_, ?_⟩, ?_⟩
  · rw [e.mem]; exact I.frame.trans F
  · rw [e.mem]
    have P := VG.Proof.Dsa.mont_product (cop _) I.val I.val V
    rw [P]
    congr 2
    simp only [x]
    rw [← Nat.pow_add, Nat.pow_succ 2 j, ← Nat.mul_assoc, Nat.mul_two]
  · rw [e.gpr, esiu]; exact c₁
  · rw [z, esiu, c₂]

end VG.Proof.Bignum.X86.PrecomputeRt
