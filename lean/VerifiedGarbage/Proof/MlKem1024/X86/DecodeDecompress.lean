import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.X86.Unpack`. -/
section

/-!
# ML-KEM-1024 on x86 (32-bit): loading bytes and decompressing coefficients

`decompOp` computes the decompress formula of `Compress1024.lean`
(`decomp_spec`), which `decSt` stores (`decSt_spec`); `bySteps` and `ldW`
combine bytes into `ebx` (`bySteps_spec`, `ldW_spec`), as the number `pk 8`
whose base-2⁸ digits they are.
-/

namespace VG.Proof.MlKem1024.X86

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

theorem dv_lt' {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : Nat} (hy : y < 2 ^ d) : dv d y < q :=
  (decompress1024_val hd hy).2

theorem dv_eq' {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : Nat} (hy : y < 2 ^ d) :
    dv d y = (decompress d y).val := (decompress1024_val hd hy).1.symm

/-- `decompOp d` computes `dv d y` in `eax` from `eax = y < 2ᵈ`, changing only `eax`, `edx` and
the flags. -/
theorem decomp_spec' {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (is : List Instr) (s : State)
    (P : State → Prop) {y : Nat} (hy : y < 2 ^ d) (h : (s.gpr .eax).toNat = y)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = dv d y → WP isa (.block is) s' P) :
    WP isa (.block (decompOp d ++ is)) s P := by
  have hd' : 1 ≤ d ∧ d ≤ 31 ∧ y < 2048 := by
    rcases mem_compressWidths1024 hd with rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩ <;> omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, decompOp, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, execMul, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', hd'.1, hd'.2.1, and_self]
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    have hp : 2 ^ (d - 1) ≤ 1024 := by
      rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
    rw [toNat_shr]
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, h]
    rw [show (3329 : BitVec 32).toNat = 3329 from rfl, Nat.mod_eq_of_lt (a := y * 3329) (by omega),
      Nat.mod_eq_of_lt (a := 2 ^ (d - 1)) (by omega), Nat.mod_eq_of_lt (by omega), dv, q_eq, Nat.mul_comm y]

/-- `decSt d j` writes `dv d y` to `[edi + 4j]`, from `eax = y < 2ᵈ`. -/
theorem decSt_spec {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (j : Nat) (is : List Instr)
    (s : State) (P : State → Prop) {y : Nat} (hy : y < 2 ^ d) (h : (s.gpr .eax).toNat = y)
    (hin : InRegions s.wr (s.ea (at_ .edi (4 * j))) 4)
    (k : ∀ s', Regs [.eax, .edx] s s' →
      s'.mem = s.mem.writeW (s.ea (at_ .edi (4 * j))) (BitVec.ofNat 32 (dv d y)) → WP isa (.block is) s' P) :
    WP isa (.block (decSt d j ++ is)) s P := by
  rw [decSt, List.append_assoc]
  refine VG.Proof.MlKem1024.X86.decomp_spec' hd _ s P hy h fun s₁ o₁ v₁ => ?_
  have ea₁ : s₁.ea (at_ .edi (4 * j)) = s.ea (at_ .edi (4 * j)) := by
    simp only [State.ea, at_, o₁.gpr .edi (by decide)]
  refine wp_store (by rw [ea₁, o₁.wr]; exact hin) ?_
  refine k _ ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr⟩ ?_
  show s₁.mem.writeW (s₁.ea (at_ .edi (4 * j))) (s₁.gpr .eax) = _
  rw [ea₁, o₁.mem, eq_ofNat_of_toNat v₁]

/-- Byte `i` from `esi`: at `[esi + i]`, readable, `v`. -/
structure Byt (s : State) (i v : Nat) : Prop where
  in_ : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi i)) 1
  val : (s.mem (s.ea (at_ .esi i))).toNat = v

theorem Byt.of_only {s s' : State} {i v : Nat} {ds : List Reg} (h : VG.Proof.MlKem1024.X86.Byt s i v) (ho : Only ds s s')
    (hesi : Reg.esi ∉ ds) : VG.Proof.MlKem1024.X86.Byt s' i v := by
  have e : s'.ea (at_ .esi i) = s.ea (at_ .esi i) := by simp only [State.ea, at_, ho.gpr _ hesi]
  exact ⟨by rw [e, ho.rd, ho.wr]; exact h.in_, by rw [e, ho.mem]; exact h.val⟩

theorem Byt.lt {s : State} {i v : Nat} (h : VG.Proof.MlKem1024.X86.Byt s i v) : v < 256 := by
  rw [← h.val]; exact (s.mem _).isLt

/-- `movzx d, byte [esi + i]`. -/
theorem wp_ldb {d : Reg} {i v : Nat} {is : List Instr} {s : State} {Q : State → Prop} (hb : VG.Proof.MlKem1024.X86.Byt s i v)
    (k : ∀ s', Only [d] s s' → (s'.gpr d).toNat = v → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ .esi i) :: is)) s Q :=
  wp_movzx hb.in_ (k _ (Only.setReg s d _) (by simp only [State.setReg, ite_true]; rw [toNat_byte32, hb.val]))

theorem bySteps_spec (o : Nat) (x : Nat → Nat) :
    ∀ (j : Nat) (is : List Instr) (s : State) (P : State → Prop) (A : Nat),
      (∀ i < j, VG.Proof.MlKem1024.X86.Byt s (o + i) (x i)) → (s.gpr .ebx).toNat = A → (A + 1) * 2 ^ (8 * j) ≤ 2 ^ 32 →
      (∀ s', Only [.eax, .ebx] s s' → (s'.gpr .ebx).toNat = A * 2 ^ (8 * j) + pk 8 x j →
        WP isa (.block is) s' P) →
      WP isa (.block (bySteps o j ++ is)) s P
  | 0, is, s, P, A, _, hA, _, k => k s (Only.refl _ _) (by simp [pk, hA])
  | j + 1, is, s, P, A, hc, hA, hb, k => by
    have hpj : 1 ≤ 2 ^ (8 * j) := Nat.one_le_two_pow
    have hsplit : 2 ^ (8 * (j + 1)) = 2 ^ 8 * 2 ^ (8 * j) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ, Nat.add_comm]
    have hAl : A < 2 ^ 24 := by
      have : (A + 1) * 2 ^ 8 ≤ 2 ^ 32 := by
        refine Nat.le_trans ?_ hb
        rw [hsplit, ← Nat.mul_assoc]
        exact Nat.le_mul_of_pos_right _ hpj
      omega
    have hx := (hc j (by omega)).lt
    rw [bySteps, byteStep, List.append_assoc, List.cons_append]
    refine VG.Proof.MlKem1024.X86.wp_ldb (hc j (by omega)) fun s₁ o₁ v₁ => ?_
    refine wp_ror (by decide) (by decide) fun s₂ o₂ e₂ => wp_addr fun s₃ o₃ e₃ => ?_
    have oo := (o₁.trans o₂).trans o₃
    have v₃ : (s₃.gpr .ebx).toNat = A * 2 ^ 8 + x j := by
      have r := ror_shl (d := 8) (A := A) (by decide) (by decide) (s₁.gpr .ebx)
        (by rw [o₁.gpr _ (by decide), hA]) hAl
      rw [e₃, BitVec.toNat_add, e₂, r, o₂.gpr .eax (by decide), v₁]
      omega
    refine VG.Proof.MlKem1024.X86.bySteps_spec o x j is s₃ P _ (fun i hi => (hc i (by omega)).of_only oo (by decide)) v₃ ?_
      fun s₄ o₄ v₄ => k s₄ ((oo.trans o₄).mono fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with ((h | h) | h) | h | h <;> simp only [h, true_or, or_true]) ?_
    · have : A * 2 ^ 8 + x j + 1 ≤ (A + 1) * 2 ^ 8 := by rw [Nat.add_mul]; omega
      refine Nat.le_trans (Nat.mul_le_mul_right _ this) ?_
      rw [Nat.mul_assoc, ← hsplit]; exact hb
    · rw [v₄, pk, hsplit, Nat.add_mul, Nat.mul_assoc]
      omega

/-- `ldW o n` loads the `n + 1` bytes at `esi + o` into `ebx`, as the number whose base-2⁸ digits
they are. -/
theorem ldW_spec (o n : Nat) (hn : n ≤ 3) (x : Nat → Nat) (is : List Instr) (s : State) (P : State → Prop)
    (hc : ∀ i < n + 1, VG.Proof.MlKem1024.X86.Byt s (o + i) (x i))
    (k : ∀ s', Only [.ebx, .eax, .ebx] s s' → (s'.gpr .ebx).toNat = pk 8 x (n + 1) → WP isa (.block is) s' P) :
    WP isa (.block (ldW o n ++ is)) s P := by
  rw [ldW, List.cons_append]
  refine VG.Proof.MlKem1024.X86.wp_ldb (hc n (by omega)) fun s₁ o₁ v₁ => ?_
  have hx := (hc n (by omega)).lt
  refine VG.Proof.MlKem1024.X86.bySteps_spec o x n is s₁ P _ (fun i hi => (hc i (by omega)).of_only o₁ (by decide)) v₁ ?_
    fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂) ?_
  · have : 2 ^ (8 * n) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
    calc (x n + 1) * 2 ^ (8 * n) ≤ 2 ^ 8 * 2 ^ 24 := Nat.mul_le_mul (by omega) this
      _ = 2 ^ 32 := by decide
  · rw [v₂, pk]; omega

end VG.Proof.MlKem1024.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress`. -/
section

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_decode_decompress`

The branch on `d` depends only on `d`; each branch is a loop over the 32
groups of `d` bytes, loaded into `ebx` by `ldW` (`Unpack.lean`), whose fields
(`fieldAt`, `crossAt`) are decompressed in order into the coefficients of
`decodeDecompress5_*` and `decodeDecompress11_*` (`Encode1024.lean`). `D b t
k` is the state within group `t` of `b` bytes, after its first `k`
coefficients.
-/

namespace VG.Proof.MlKem1024.X86.DecodeDecompress

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem1024.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev bP : BitVec 32 := arg s₀ 0
abbrev lenV : BitVec 32 := arg s₀ 1
abbrev dV : BitVec 32 := arg s₀ 2
abbrev fP : BitVec 32 := arg s₀ 3
abbrev bA : Addr := (VG.Proof.MlKem1024.X86.DecodeDecompress.bP s₀).setWidth 64
abbrev fA : Addr := (VG.Proof.MlKem1024.X86.DecodeDecompress.fP s₀).setWidth 64
abbrev bR : Region := ⟨VG.Proof.MlKem1024.X86.DecodeDecompress.bA s₀, (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev dN : Nat := (VG.Proof.MlKem1024.X86.DecodeDecompress.dV s₀).toNat
/-- The input bytes. -/
abbrev B : List Byte := bytesAt s₀.mem (VG.Proof.MlKem1024.X86.DecodeDecompress.bA s₀) (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat
/-- The value of coefficient `i`. -/
abbrev V (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress (VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀) (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀))[i]!).val
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀), VG.Proof.MlKem1024.X86.DecodeDecompress.aR s₀]
  b_f : (VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀).Disjoint (polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀))
  b_a : (VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀).Disjoint (VG.Proof.MlKem1024.X86.DecodeDecompress.aR s₀)
  f_a : (polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀)).Disjoint (VG.Proof.MlKem1024.X86.DecodeDecompress.aR s₀)
  ret_b : (retR s₀).Disjoint (VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlKem1024.X86.DecodeDecompress.aR s₀)
  stk_b : (VG.Proof.MlKem1024.X86.DecodeDecompress.stkR s₀).Disjoint (VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀)
  stk_f : (VG.Proof.MlKem1024.X86.DecodeDecompress.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀))
  stk_a : (VG.Proof.MlKem1024.X86.DecodeDecompress.stkR s₀).Disjoint (VG.Proof.MlKem1024.X86.DecodeDecompress.aR s₀)
  b_fit : (VG.Proof.MlKem1024.X86.DecodeDecompress.bP s₀).toNat + (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat ≤ 2 ^ 32
  f_fit : (VG.Proof.MlKem1024.X86.DecodeDecompress.fP s₀).toNat + 1024 ≤ 2 ^ 32
  d_mem : VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ ∈ Spec.MlKem1024.compressWidths
  len_eq : (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat = 32 * VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀

theorem Pre.of {s₀ : State} (h : (Spec.MlKem1024.decodeDecompressContract X86.abi 16).pre s₀) : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀ := by
  sig_pre [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀)
include hp

theorem stk_eq : VG.Proof.MlKem1024.X86.DecodeDecompress.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlKem1024.X86.DecodeDecompress.stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem b_keep {s : State} (hf : Frame [polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀)] (P0 s₀).mem s.mem) {j : Nat}
    (hj : j < (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat) : s.mem (VG.Proof.MlKem1024.X86.DecodeDecompress.bA s₀ + BitVec.ofNat 64 j) = (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD j 0 := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  have l : (VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀).len ≤ 2 ^ 64 := by show (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat ≤ 2 ^ 64; have := (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).isLt; omega
  rw [bytesAt_getD _ _ hj, hf.bytes (R := VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀) (by simpa using hp.b_f) l hj,
    hf₁.bytes (R := VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀) (by simpa [← hp.stk_eq] using hp.stk_b.symm) l hj]

theorem B_len : (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).length = 32 * VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ := by rw [VG.Proof.MlKem1024.X86.DecodeDecompress.B, bytesAt_length, hp.len_eq]

end Pre

/-- Within group `t` of `b` bytes, after its first `k` coefficients, counting down from 32. -/
structure D (s₀ : State) (b t k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem1024.X86.DecodeDecompress.bP s₀ + BitVec.ofNat 32 (b * t)
  edi : s.gpr .edi = VG.Proof.MlKem1024.X86.DecodeDecompress.fP s₀ + BitVec.ofNat 32 (32 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (32 - t)
  frame : Frame [polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 8 * t + k, coeffAt s.mem (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀) i = VG.Proof.MlKem1024.X86.DecodeDecompress.V s₀ i

theorem D.of_only {s₀ s s' : State} {b t k : Nat} (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t k s) {ds : List Reg} (o : Only ds s s')
    (hd : Reg.esp ∉ ds ∧ Reg.esi ∉ ds ∧ Reg.edi ∉ ds ∧ Reg.ecx ∉ ds) : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t k s' :=
  ⟨by rw [o.gpr _ hd.1, h.esp], by rw [o.rd, h.rd], by rw [o.wr, h.wr], by rw [o.gpr _ hd.2.1, h.esi],
    by rw [o.gpr _ hd.2.2.1, h.edi], by rw [o.gpr _ hd.2.2.2, h.ecx], o.mem ▸ h.frame,
    fun j hj => o.mem ▸ h.coef j hj⟩

/-- The end of every branch. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 256, coeffAt s.mem (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀) i = VG.Proof.MlKem1024.X86.DecodeDecompress.V s₀ i

theorem D.fin {s₀ s : State} {b : Nat} (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b 32 0 s) : VG.Proof.MlKem1024.X86.DecodeDecompress.Fin s₀ s :=
  ⟨h.esp, h.rd, h.wr, h.frame, fun i hi => h.coef i (by omega)⟩

/-- Byte `o` of group `t`, from `esi`. -/
theorem D.byte {s₀ s : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀) {b t k : Nat} (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t k s) {o : Nat}
    (ho : b * t + o < (VG.Proof.MlKem1024.X86.DecodeDecompress.lenV s₀).toNat) : VG.Proof.MlKem1024.X86.Byt s o ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (b * t + o) 0).toNat := by
  have fb := hp.b_fit
  have e : s.ea (at_ .esi o) = VG.Proof.MlKem1024.X86.DecodeDecompress.bA s₀ + BitVec.ofNat 64 (b * t + o) := by
    show (s.gpr .esi + BitVec.ofNat 32 o).setWidth 64 = _
    rw [h.esi, ea_add (by omega)]
  refine ⟨?_, ?_⟩
  · rw [e]; exact ⟨VG.Proof.MlKem1024.X86.DecodeDecompress.bR s₀, by rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]; simp, contains_at (by omega) fb⟩
  · rw [e, hp.b_keep h.frame ho]

/-- Coefficient `8 t + k` from `eax = y`. -/
theorem D.st {s₀ s : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀) {d b t k : Nat} (hd : VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d) (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t k s) (ht : t < 32)
    (hk : k < 8) {y : Nat} (hy : y < 2 ^ d) (hax : (s.gpr .eax).toNat = y)
    (hv : (decodeDecompress d (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀))[8 * t + k]! = decompress d y) {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t (k + 1) s' → s'.gpr .ebx = s.gpr .ebx → WP isa (.block is) s' Q) :
    WP isa (.block (decSt d k ++ is)) s Q := by
  have hdm : d ∈ Spec.MlKem1024.compressWidths := hd ▸ hp.d_mem
  have ff := hp.f_fit
  have e : s.ea (at_ .edi (4 * k)) = coeffAddr (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀) (8 * t + k) := by
    show (s.gpr .edi + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [h.edi, ea_add (by omega)]
    congr 2; omega
  have hn : 8 * t + k < n := by rw [n_eq]; omega
  refine VG.Proof.MlKem1024.X86.decSt_spec hdm k is s Q hy hax
    ⟨polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, by rw [e]; exact coeff_contains _ hn⟩
    fun s' r m => kk s' ⟨by rw [r.gpr _ (by decide), h.esp], by rw [r.rd, h.rd], by rw [r.wr, h.wr],
      by rw [r.gpr _ (by decide), h.esi], by rw [r.gpr _ (by decide), h.edi], by rw [r.gpr _ (by decide), h.ecx],
      ?_, ?_⟩ (r.gpr _ (by decide))
  · rw [m, e]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn)
  · intro i hi
    rw [m, e, coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) hn]
    by_cases ei : 8 * t + k = i
    · rw [ite_eq_left ei, ← ei, VG.Proof.MlKem1024.X86.DecodeDecompress.V, hd, hv, VG.Proof.MlKem1024.X86.dv_eq' hdm hy]
    · rw [ite_eq_right ei]; exact h.coef i (by omega)

/-- Coefficient `8 t + k`, the field of `ebx = W` at bit `sh`. -/
theorem D.field {s₀ s : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀) {d b t k : Nat} (hd : VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d) (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t k s) (ht : t < 32)
    (hk : k < 8) {W : Nat} (hW : (s.gpr .ebx).toNat = W) {sh : Nat} (hsh : sh ≤ 31)
    (hv : (decodeDecompress d (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀))[8 * t + k]! = decompress d (W / 2 ^ sh % 2 ^ d)) {is : List Instr}
    {Q : State → Prop} (kk : ∀ s', VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t (k + 1) s' → s'.gpr .ebx = s.gpr .ebx → WP isa (.block is) s' Q) :
    WP isa (.block (fieldAt d sh k ++ is)) s Q := by
  have hdm : d ∈ Spec.MlKem1024.compressWidths := hd ▸ hp.d_mem
  have hd' : d < 32 := by rcases mem_compressWidths1024 hdm with rfl | rfl <;> decide
  rw [fieldAt, List.append_assoc, List.cons_append]
  refine shrFrom_spec sh hsh _ s Q fun s₁ o₁ v₁ => wp_and fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine (h.of_only o (by decide)).st hp hd ht hk (Nat.mod_lt _ (Nat.two_pow_pos d)) ?_ hv fun s' h' e' => ?_
  · rw [v₂, v₁, toNat_and_mask _ _ hd', toNat_shr, hW]
  · exact kk s' h' (by rw [e', o.gpr _ (by decide)])

/-- Coefficient `8 t + k`, the field of `ebx = W` at bit `sh` continued by the low `e` bits of
byte `o`, at bit `m` of the field. -/
theorem D.cross {s₀ s : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀) {d b t k : Nat} (hd : VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d) (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t k s) (ht : t < 32)
    (hk : k < 8) {W : Nat} (hW : (s.gpr .ebx).toNat = W) {sh o e m : Nat} (hsh : 1 ≤ sh ∧ sh ≤ 31)
    (hm : 1 ≤ m ∧ m ≤ 31) (hem : e + m ≤ 32) (he : e < 32) {x : Nat} (hx : VG.Proof.MlKem1024.X86.Byt s o x)
    (hy : W / 2 ^ sh + x % 2 ^ e * 2 ^ m < 2 ^ d)
    (hv : (decodeDecompress d (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀))[8 * t + k]! = decompress d (W / 2 ^ sh + x % 2 ^ e * 2 ^ m))
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t (k + 1) s' → s'.gpr .ebx = s.gpr .ebx → WP isa (.block is) s' Q) :
    WP isa (.block (crossAt d sh o e m k ++ is)) s Q := by
  have hW' : W < 2 ^ 32 := by rw [← hW]; exact (s.gpr .ebx).isLt
  rw [crossAt, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.MlKem1024.X86.wp_ldb hx fun s₁ o₁ v₁ => wp_and fun s₂ o₂ v₂ => wp_ror (by omega) (by omega) fun s₃ o₃ v₃ => ?_
  refine wp_mov fun s₄ o₄ v₄ => wp_shr hsh.1 hsh.2 fun s₅ o₅ v₅ => wp_addr fun s₆ o₆ v₆ => ?_
  have o := (((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆)
  have hxe : (s₂.gpr .edx).toNat = x % 2 ^ e := by rw [v₂, toNat_and_mask _ _ he, v₁]
  have hxl : x % 2 ^ e < 2 ^ (32 - m) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos e)) (Nat.pow_le_pow_right (by decide) (by omega))
  have r := ror_shl (d := m) hm.1 (by omega) (s₂.gpr .edx) hxe hxl
  have h32 : 2 ^ d ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by
    have := hp.d_mem; rw [hd] at this; rcases mem_compressWidths1024 this with rfl | rfl <;> decide)
  have hsum : W / 2 ^ sh + x % 2 ^ e * 2 ^ m < 2 ^ 32 := Nat.lt_of_lt_of_le hy h32
  refine (h.of_only o (by decide)).st hp hd ht hk hy ?_ hv fun s' h' e' => ?_
  · rw [v₆, BitVec.toNat_add, v₅, v₄, o₃.gpr .ebx (by decide), o₂.gpr .ebx (by decide), o₁.gpr .ebx (by decide),
      toNat_shr, hW, o₅.gpr .edx (by decide), o₄.gpr .edx (by decide), v₃, r, Nat.mod_eq_of_lt hsum]
  · exact kk s' h' (by rw [e', o.gpr _ (by decide)])

/-- The end of a group: on to the next. -/
theorem next_spec {s₀ s : State} {b t : Nat} (ht : t < 32) (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b t 8 s) :
    WP isa (.block (nextG b 32)) s fun s' => VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, nextG, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, ?_, ?_, ?_, h.frame, fun j hj => h.coef j (by rw [Nat.mul_succ] at hj; omega)⟩,
    ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true, h.esi]
    rw [add_ofNat_add, Nat.mul_succ]
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.edi]
    rw [add_ofNat_add, Nat.mul_succ]
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## `d` = 5: eight coefficients of five bytes -/

theorem step5 {s₀ : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀) (hd : VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = 5) {t : Nat} (ht : t < 32) {s : State}
    (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ 5 t 0 s) :
    WP isa (.block unpack5Body) s fun s' => VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ 5 (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  have hl := hp.len_eq
  rw [hd] at hl
  have hB : (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).length = 160 := by rw [hp.B_len, hd]
  have lb : ∀ i, ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (5 * t + i) 0).toNat < 256 := fun i => byte_lt _
  have l0 := lb 0
  have l1 := lb 1
  have l2 := lb 2
  have l3 := lb 3
  have l4 := lb 4
  simp only [Nat.add_zero] at l0
  unfold unpack5Body
  refine VG.Proof.MlKem1024.X86.ldW_spec 0 3 (by decide) (fun i => ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (5 * t + i) 0).toNat) _ s _
    (fun i hi => by rw [Nat.zero_add]; exact h.byte hp (by omega)) fun s₁ o₁ v₁ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow] at v₁
  have h₁ := h.of_only o₁ (by decide)
  refine h₁.field hp hd ht (k := 0) (by decide) v₁ (sh := 0) (by decide) ?_ fun s₂ h₂ e₂ => ?_
  · rw [Nat.add_zero, decodeDecompress5_0 _ hB ht]; refine congrArg (decompress 5) ?_
    omega_using [l0, l1, l2, l3, l4]
  refine h₂.field hp hd ht (k := 1) (by decide) ((congrArg BitVec.toNat (e₂)).trans v₁) (sh := 5) (by decide) ?_
    fun s₃ h₃ e₃ => ?_
  · rw [decodeDecompress5_1 _ hB ht]; refine congrArg (decompress 5) ?_; omega_using [l0, l1, l2, l3, l4]
  refine h₃.field hp hd ht (k := 2) (by decide) ((congrArg BitVec.toNat ((e₃).trans e₂)).trans v₁) (sh := 10) (by decide) ?_
    fun s₄ h₄ e₄ => ?_
  · rw [decodeDecompress5_2 _ hB ht]; refine congrArg (decompress 5) ?_; omega_using [l0, l1, l2, l3, l4]
  refine h₄.field hp hd ht (k := 3) (by decide) ((congrArg BitVec.toNat (((e₄).trans e₃).trans e₂)).trans v₁) (sh := 15) (by decide) ?_
    fun s₅ h₅ e₅ => ?_
  · rw [decodeDecompress5_3 _ hB ht]; refine congrArg (decompress 5) ?_; omega_using [l0, l1, l2, l3, l4]
  refine h₅.field hp hd ht (k := 4) (by decide) ((congrArg BitVec.toNat ((((e₅).trans e₄).trans e₃).trans e₂)).trans v₁) (sh := 20) (by decide) ?_
    fun s₆ h₆ e₆ => ?_
  · rw [decodeDecompress5_4 _ hB ht]; refine congrArg (decompress 5) ?_; omega_using [l0, l1, l2, l3, l4]
  refine h₆.field hp hd ht (k := 5) (by decide) ((congrArg BitVec.toNat (((((e₆).trans e₅).trans e₄).trans e₃).trans e₂)).trans v₁) (sh := 25) (by decide) ?_
    fun s₇ h₇ e₇ => ?_
  · rw [decodeDecompress5_5 _ hB ht]; refine congrArg (decompress 5) ?_; omega_using [l0, l1, l2, l3, l4]
  refine h₇.cross hp hd ht (k := 6) (by decide) ((congrArg BitVec.toNat ((((((e₇).trans e₆).trans e₅).trans e₄).trans e₃).trans e₂)).trans v₁) (sh := 30) (o := 4)
    (e := 3) (m := 2) (by decide) (by decide) (by decide) (by decide) (h₇.byte hp (o := 4) (by omega)) ?_ ?_
    fun s₈ h₈ _ => ?_
  · simp only [Nat.reducePow]; omega_using [l0, l1, l2, l3, l4]
  · rw [decodeDecompress5_6 _ hB ht]; refine congrArg (decompress 5) ?_; simp only [Nat.reducePow]
    omega_using [l0, l1, l2, l3, l4]
  refine VG.Proof.MlKem1024.X86.ldW_spec 4 0 (by decide) (fun i => ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (5 * t + (4 + i)) 0).toNat) _ s₈ _
    (fun i hi => h₈.byte hp (by omega)) fun s₉ o₉ v₉ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at v₉
  refine (h₈.of_only o₉ (by decide)).field hp hd ht (k := 7) (by decide) v₉ (sh := 3) (by decide) ?_
    fun s₁₀ h₁₀ _ => VG.Proof.MlKem1024.X86.DecodeDecompress.next_spec ht h₁₀
  rw [decodeDecompress5_7 _ hB ht]; refine congrArg (decompress 5) ?_; omega_using [l0, l1, l2, l3, l4]

/-! ## `d` = 11: eight coefficients of eleven bytes -/

theorem step11 {s₀ : State} (hp : VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀) (hd : VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = 11) {t : Nat} (ht : t < 32) {s : State}
    (h : VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ 11 t 0 s) :
    WP isa (.block unpack11Body) s fun s' => VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ 11 (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  have hl := hp.len_eq
  rw [hd] at hl
  have hB : (VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).length = 352 := by rw [hp.B_len, hd]
  have lb : ∀ i, ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (11 * t + i) 0).toNat < 256 := fun i => byte_lt _
  have l0 := lb 0
  have l1 := lb 1
  have l2 := lb 2
  have l3 := lb 3
  have l4 := lb 4
  have l5 := lb 5
  have l6 := lb 6
  have l7 := lb 7
  have l8 := lb 8
  have l9 := lb 9
  have l10 := lb 10
  simp only [Nat.add_zero] at l0
  unfold unpack11Body
  -- Bytes 0–3.
  refine VG.Proof.MlKem1024.X86.ldW_spec 0 3 (by decide) (fun i => ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (11 * t + i) 0).toNat) _ s _
    (fun i hi => by rw [Nat.zero_add]; exact h.byte hp (by omega)) fun s₁ o₁ v₁ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow] at v₁
  have h₁ := h.of_only o₁ (by decide)
  refine h₁.field hp hd ht (k := 0) (by decide) v₁ (sh := 0) (by decide) ?_ fun s₂ h₂ e₂ => ?_
  · rw [Nat.add_zero, decodeDecompress11_0 _ hB ht]; refine congrArg (decompress 11) ?_
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  refine h₂.field hp hd ht (k := 1) (by decide) ((congrArg BitVec.toNat (e₂)).trans v₁) (sh := 11) (by decide) ?_
    fun s₃ h₃ e₃ => ?_
  · rw [decodeDecompress11_1 _ hB ht]; refine congrArg (decompress 11) ?_
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  refine h₃.cross hp hd ht (k := 2) (by decide) ((congrArg BitVec.toNat ((e₃).trans e₂)).trans v₁) (sh := 22) (o := 4)
    (e := 1) (m := 10) (by decide) (by decide) (by decide) (by decide) (h₃.byte hp (o := 4) (by omega)) ?_ ?_
    fun s₄ h₄ _ => ?_
  · simp only [Nat.reducePow]; omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  · rw [decodeDecompress11_2 _ hB ht]; refine congrArg (decompress 11) ?_; simp only [Nat.reducePow]
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  -- Bytes 4–7.
  refine VG.Proof.MlKem1024.X86.ldW_spec 4 3 (by decide) (fun i => ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (11 * t + (4 + i)) 0).toNat) _ s₄ _
    (fun i hi => h₄.byte hp (by omega)) fun s₅ o₅ v₅ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow, Nat.reduceAdd] at v₅
  have h₅ := h₄.of_only o₅ (by decide)
  refine h₅.field hp hd ht (k := 3) (by decide) v₅ (sh := 1) (by decide) ?_ fun s₆ h₆ e₆ => ?_
  · rw [decodeDecompress11_3 _ hB ht]; refine congrArg (decompress 11) ?_
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  refine h₆.field hp hd ht (k := 4) (by decide) ((congrArg BitVec.toNat (e₆)).trans v₅) (sh := 12) (by decide) ?_
    fun s₇ h₇ e₇ => ?_
  · rw [decodeDecompress11_4 _ hB ht]; refine congrArg (decompress 11) ?_
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  refine h₇.cross hp hd ht (k := 5) (by decide) ((congrArg BitVec.toNat ((e₇).trans e₆)).trans v₅) (sh := 23) (o := 8)
    (e := 2) (m := 9) (by decide) (by decide) (by decide) (by decide) (h₇.byte hp (o := 8) (by omega)) ?_ ?_
    fun s₈ h₈ _ => ?_
  · simp only [Nat.reducePow]; omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  · rw [decodeDecompress11_5 _ hB ht]; refine congrArg (decompress 11) ?_; simp only [Nat.reducePow]
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  -- Bytes 8–10.
  refine VG.Proof.MlKem1024.X86.ldW_spec 8 2 (by decide) (fun i => ((VG.Proof.MlKem1024.X86.DecodeDecompress.B s₀).getD (11 * t + (8 + i)) 0).toNat) _ s₈ _
    (fun i hi => h₈.byte hp (by omega)) fun s₉ o₉ v₉ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow, Nat.reduceAdd] at v₉
  have h₉ := h₈.of_only o₉ (by decide)
  refine h₉.field hp hd ht (k := 6) (by decide) v₉ (sh := 2) (by decide) ?_ fun s₁₀ h₁₀ e₁₀ => ?_
  · rw [decodeDecompress11_6 _ hB ht]; refine congrArg (decompress 11) ?_
    omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]
  refine h₁₀.field hp hd ht (k := 7) (by decide) ((congrArg BitVec.toNat (e₁₀)).trans v₉) (sh := 13) (by decide) ?_
    fun s₁₁ h₁₁ _ => VG.Proof.MlKem1024.X86.DecodeDecompress.next_spec ht h₁₁
  rw [decodeDecompress11_7 _ hB ht]; refine congrArg (decompress 11) ?_
  omega_using [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10]

/-! ## The function -/

/-- After `ddInit5`. -/
structure Init (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = VG.Proof.MlKem1024.X86.DecodeDecompress.bP s₀
  edi : s.gpr .edi = VG.Proof.MlKem1024.X86.DecodeDecompress.fP s₀
  ev : eval .e s = some (decide (VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = 5))

theorem pub_esp {s₀ s₀' : State} (hq : VG.Proof.MlKem1024.X86.DecodeDecompress.Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

theorem init_piece : Piece VG.Proof.MlKem1024.X86.DecodeDecompress.Pre VG.Proof.MlKem1024.X86.DecodeDecompress.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem1024.X86.DecodeDecompress.Init (.block ddInit5) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₂ := P0_argAddr s₀ 2
    have a₃ := P0_argAddr s₀ 3
    have i₀ := P0_argIn (s₀ := s₀) (n := 4) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₂ := P0_argIn (s₀ := s₀) (n := 4) (i := 2) (by omega) fit (by simp [hp.wr])
    have i₃ := P0_argIn (s₀ := s₀) (n := 4) (i := 3) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 4) (i := 0) (by omega) fit hp.stk_a
    have v₂ := P0_arg hp.sp (n := 4) (i := 2) (by omega) fit hp.stk_a
    have v₃ := P0_arg hp.sp (n := 4) (i := 3) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a₀ a₂ a₃
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, ddInit5, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₂, a₃, i₀, i₂, i₃, v₀, v₂, v₃,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', VG.Proof.MlKem1024.X86.DecodeDecompress.pub_esp hq]

theorem ecx_piece (d b : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) hc).isSome = true) :
    Piece VG.Proof.MlKem1024.X86.DecodeDecompress.Pre VG.Proof.MlKem1024.X86.DecodeDecompress.Pub (fun s₀ s => VG.Proof.MlKem1024.X86.DecodeDecompress.Init s₀ s ∧ VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d)
      (fun s₀ s => VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ b 0 0 s ∧ VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hd⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    ht
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp [h.edi], by simp,
    (by rw [h.mem]; exact Frame.refl _ _), fun j hj => absurd hj (by omega)⟩, hd⟩

theorem branch_piece {d : Nat} (body : List Instr)
    (hstep : ∀ t < 32, ∀ s₀ s, VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀ → VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d → VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ d t 0 s →
      WP isa (.block body) s fun s' => VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ d (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true)
    {hc' : Taint.Hint VG.X86.Taint.T}
    (ht' : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) hc').isSome = true) :
    Piece VG.Proof.MlKem1024.X86.DecodeDecompress.Pre VG.Proof.MlKem1024.X86.DecodeDecompress.Pub (fun s₀ s => VG.Proof.MlKem1024.X86.DecodeDecompress.Init s₀ s ∧ VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d) VG.Proof.MlKem1024.X86.DecodeDecompress.Fin (countedLoop 32 body) :=
  (Piece.seq (VG.Proof.MlKem1024.X86.DecodeDecompress.ecx_piece d d ht') (Piece.countLoop (by decide) (fun t s₀ s => VG.Proof.MlKem1024.X86.DecodeDecompress.D s₀ d t 0 s ∧ VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = d)
    [.esp, .esi, .edi, .ecx]
    (fun t ht s₀ s hp ⟨h, hd⟩ => (hstep t ht s₀ s hp hd h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hd⟩, e⟩)
    (fun t _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, VG.Proof.MlKem1024.X86.DecodeDecompress.pub_esp hq]
      · rw [h.esi, h'.esi, VG.Proof.MlKem1024.X86.DecodeDecompress.bP, VG.Proof.MlKem1024.X86.DecodeDecompress.bP, hq.2.1]
      · rw [h.edi, h'.edi, VG.Proof.MlKem1024.X86.DecodeDecompress.fP, VG.Proof.MlKem1024.X86.DecodeDecompress.fP, hq.2.2.2.2]
      · rw [h.ecx, h'.ecx]) ht)).mono (fun _ _ _ h => h) fun _ _ _ ⟨h, _⟩ => h.fin

theorem ite_pub : ∀ s₀ s₀', VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀ → VG.Proof.MlKem1024.X86.DecodeDecompress.Pre s₀' → VG.Proof.MlKem1024.X86.DecodeDecompress.Pub s₀ s₀' →
    decide (VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀ = 5) = decide (VG.Proof.MlKem1024.X86.DecodeDecompress.dN s₀' = 5) := fun _ _ _ _ hq => by rw [VG.Proof.MlKem1024.X86.DecodeDecompress.dN, VG.Proof.MlKem1024.X86.DecodeDecompress.dN, VG.Proof.MlKem1024.X86.DecodeDecompress.dV, VG.Proof.MlKem1024.X86.DecodeDecompress.dV, hq.2.2.2.1]

theorem body_piece : Piece VG.Proof.MlKem1024.X86.DecodeDecompress.Pre VG.Proof.MlKem1024.X86.DecodeDecompress.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem1024.X86.DecodeDecompress.Fin
    (.seq (.block ddInit5) (.ite .e (countedLoop 32 unpack5Body) (countedLoop 32 unpack11Body))) := by
  refine Piece.seq VG.Proof.MlKem1024.X86.DecodeDecompress.init_piece (Piece.ite _ (fun _ _ _ h => h.ev) VG.Proof.MlKem1024.X86.DecodeDecompress.ite_pub ?_ ?_)
  · exact (VG.Proof.MlKem1024.X86.DecodeDecompress.branch_piece (d := 5) unpack5Body (fun t ht s₀ s hp hd h => VG.Proof.MlKem1024.X86.DecodeDecompress.step5 hp hd ht h) (by taint_decide)
      (by taint_decide)).mono (fun _ _ _ ⟨h, e⟩ => ⟨h, of_decide_eq_true e⟩) fun _ _ _ h => h
  · exact (VG.Proof.MlKem1024.X86.DecodeDecompress.branch_piece (d := 11) unpack11Body (fun t ht s₀ s hp hd h => VG.Proof.MlKem1024.X86.DecodeDecompress.step11 hp hd ht h) (by taint_decide)
      (by taint_decide)).mono
      (fun s₀ _ hp ⟨h, e⟩ => ⟨h, by
        have h5 := of_decide_eq_false e
        rcases mem_compressWidths1024 hp.d_mem with h' | h' <;> [exact absurd h' h5; exact h']⟩)
      fun _ _ _ h => h

theorem piece : Piece VG.Proof.MlKem1024.X86.DecodeDecompress.Pre VG.Proof.MlKem1024.X86.DecodeDecompress.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem1024.X86.DecodeDecompress.Fin s₀) s₀ s')
    Impl.MlKem1024.X86.decodeDecompress :=
  Piece.leaf (fun s₀ => [polyRegion (VG.Proof.MlKem1024.X86.DecodeDecompress.fA s₀)]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `160`, `5` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 160 else if a = 0x500c then 5 else if a = 0x5011 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.decodeDecompress
    (Spec.MlKem1024.decodeDecompressContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.coef i (by rw [n_eq] at hi; exact hi)
  · let st := satState VG.Proof.MlKem1024.X86.DecodeDecompress.satMem [⟨0, 160⟩] [⟨0x400, 1024⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem1024.X86.DecodeDecompress

end
