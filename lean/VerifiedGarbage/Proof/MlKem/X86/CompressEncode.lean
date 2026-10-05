import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86.Compress
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Pack`. -/
section

/-!
# ML-KEM on x86 (32-bit): compressing and packing coefficients

`compOp` computes the compress formula of `Compress.lean` (`comp_spec`);
`accStep` packs one more compressed coefficient into `ebx` (`accStep_spec`),
and `accSteps` packs `j` of them, from `j - 1` down to 0 (`accSteps_spec`), as
the number `pk` whose base-`2ᵈ` digits they are.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- The compress formula, on the integer `a`. -/
def cf (d a : Nat) : Nat := (a * compressMul d + compressAdd) / 2 ^ 19 % 2 ^ d

theorem cf_lt (d a : Nat) : VG.Proof.MlKem.X86.cf d a < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

theorem cf_eq {d : Nat} (hd : d ∈ compressWidths) {a : Nat} (ha : a < q) :
    VG.Proof.MlKem.X86.cf d a = compress d (ofNat a) := by
  rw [compress_eq hd, ofNat_of_lt ha, VG.Proof.MlKem.X86.cf]

theorem cmul_eq (d : Nat) : cmul d = compressMul d := rfl

/-- `compOp d` computes `cf d a` in `eax` from `eax = a < q`, changing only `eax`, `edx` and the
flags. -/
theorem comp_spec {d : Nat} (hd : d ∈ compressWidths) (is : List Instr) (s : State) (P : State → Prop)
    {a : Nat} (ha : a < q) (h : (s.gpr .eax).toNat = a)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = VG.Proof.MlKem.X86.cf d a → WP isa (.block is) s' P) :
    WP isa (.block (compOp d ++ is)) s P := by
  have hd' : d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
  have hl := compress_arg_lt hd (ofNat a)
  rw [ofNat_of_lt ha] at hl
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, compOp, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, execMul, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    rw [toNat_and_mask _ _ hd', toNat_shr]
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, h]
    have hm : cmul d < 2 ^ 32 := by
      rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [Nat.mod_eq_of_lt hm, show (262080 : BitVec 32).toNat = compressAdd from rfl, VG.Proof.MlKem.X86.cmul_eq,
      Nat.mod_eq_of_lt (a := a * compressMul d) (by unfold compressAdd at hl; omega),
      Nat.mod_eq_of_lt (a := a * compressMul d + compressAdd) (by omega)]
    rfl

/-- Coefficient `i` from `esi`: at `[esi + 4i]`, readable, the integer `a < q`. -/
structure Coef (s : State) (i a : Nat) : Prop where
  in_ : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi (4 * i))) 4
  val : (s.mem.readW (s.ea (at_ .esi (4 * i))) 32).toNat = a
  lt : a < q

theorem Coef.of_only {s s' : State} {i a : Nat} {ds : List Reg} (h : VG.Proof.MlKem.X86.Coef s i a) (ho : Only ds s s')
    (hesi : Reg.esi ∉ ds) : VG.Proof.MlKem.X86.Coef s' i a := by
  have e : s'.ea (at_ .esi (4 * i)) = s.ea (at_ .esi (4 * i)) := by
    simp only [State.ea, at_, ho.gpr _ hesi]
  exact ⟨by rw [e, ho.rd, ho.wr]; exact h.in_, by rw [e, ho.mem]; exact h.val, h.lt⟩

/-- `mov eax, [esi + 4j]`, then `compOp d`. -/
theorem ldComp_spec {d : Nat} (hd : d ∈ compressWidths) (j : Nat) (is : List Instr) (s : State)
    (P : State → Prop) {a : Nat} (hc : VG.Proof.MlKem.X86.Coef s j a)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = VG.Proof.MlKem.X86.cf d a → WP isa (.block is) s' P) :
    WP isa (.block (.mov .eax (.mem (at_ .esi (4 * j))) :: (compOp d ++ is))) s P :=
  wp_movm hc.in_ (VG.Proof.MlKem.X86.comp_spec hd is _ P hc.lt (by simp only [State.setReg, ite_true]; exact hc.val)
    fun s' o v => k s' ⟨fun r hr => by
      rw [o.gpr r hr]; simp only [State.setReg]
      rw [ite_eq_right_iff.mpr fun (e : r = .eax) => absurd (e ▸ List.mem_cons_self ..) hr], o.mem, o.rd, o.wr⟩ v)

theorem ror_shl {A d : Nat} (hd0 : 0 < d) (hd : d < 32) (x : BitVec 32) (hx : x.toNat = A)
    (hA : A < 2 ^ (32 - d)) : (x.rotateRight (32 - d)).toNat = A * 2 ^ d := by
  rw [rotr_small x (by omega) (by omega) (by rw [hx]; exact hA), hx, show 32 - (32 - d) = d by omega]

theorem accStep_spec {d : Nat} (hd : d ∈ compressWidths) (j : Nat) (is : List Instr) (s : State)
    (P : State → Prop) {a A : Nat} (hc : VG.Proof.MlKem.X86.Coef s j a) (hA : (s.gpr .ebx).toNat = A)
    (hAl : A < 2 ^ (32 - d))
    (k : ∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = A * 2 ^ d + VG.Proof.MlKem.X86.cf d a →
      WP isa (.block is) s' P) :
    WP isa (.block (accStep d j ++ is)) s P := by
  have hd' : 0 < d ∧ d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
  rw [accStep, List.append_assoc, List.cons_append]
  refine VG.Proof.MlKem.X86.ldComp_spec hd j _ s P hc fun s₁ o₁ v₁ => ?_
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', show 1 ≤ 32 - d by omega, show 32 - d ≤ 31 by omega, and_self]
  refine k _ ⟨fun r hr => ?_, o₁.mem, o₁.rd, o₁.wr⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2, ite_false]
    exact o₁.gpr r (by simp [hr.1, hr.2.1])
  · simp only [ite_true]
    have hb : (s₁.gpr .ebx).toNat = A := by rw [o₁.gpr _ (by decide), hA]
    have hc' := VG.Proof.MlKem.X86.cf_lt d a
    have hp : A * 2 ^ d + 2 ^ d ≤ 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ d) (show A + 1 ≤ 2 ^ (32 - d) by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel (by omega)] at this
      exact this
    rw [BitVec.toNat_add, VG.Proof.MlKem.X86.ror_shl hd'.1 hd'.2 _ hb hAl, v₁, Nat.mod_eq_of_lt (by omega)]

/-- `Σ_{i<j} cv i · 2^(d i)`: the number whose base-`2ᵈ` digits are `cv 0 … cv (j - 1)`. -/
def pk (d : Nat) (cv : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => VG.Proof.MlKem.X86.pk d cv j + cv j * 2 ^ (d * j)

theorem accSteps_spec {d : Nat} (hd : d ∈ compressWidths) (a : Nat → Nat) :
    ∀ (j : Nat) (is : List Instr) (s : State) (P : State → Prop) (A : Nat),
      (∀ i < j, VG.Proof.MlKem.X86.Coef s i (a i)) → (s.gpr .ebx).toNat = A → (A + 1) * 2 ^ (d * j) ≤ 2 ^ 32 →
      (∀ s', Only [.eax, .edx, .ebx] s s' →
        (s'.gpr .ebx).toNat = A * 2 ^ (d * j) + VG.Proof.MlKem.X86.pk d (fun i => VG.Proof.MlKem.X86.cf d (a i)) j → WP isa (.block is) s' P) →
      WP isa (.block (accSteps d j ++ is)) s P
  | 0, is, s, P, A, _, hA, _, k => k s (Only.refl _ _) (by simp [VG.Proof.MlKem.X86.pk, hA])
  | j + 1, is, s, P, A, hc, hA, hb, k => by
    have hd' : 0 < d ∧ d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    have hpj : 1 ≤ 2 ^ (d * j) := Nat.one_le_two_pow
    have hsplit : 2 ^ (d * (j + 1)) = 2 ^ d * 2 ^ (d * j) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ, Nat.add_comm]
    have hAl : A < 2 ^ (32 - d) := by
      have h1 : (A + 1) * 2 ^ d ≤ 2 ^ (32 - d) * 2 ^ d := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        refine Nat.le_trans ?_ hb
        rw [hsplit, ← Nat.mul_assoc]
        exact Nat.le_mul_of_pos_right _ hpj
      have := Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos d)
      omega
    rw [accSteps, List.append_assoc]
    refine VG.Proof.MlKem.X86.accStep_spec hd j _ s P (hc j (by omega)) hA hAl fun s₁ o₁ v₁ => ?_
    refine VG.Proof.MlKem.X86.accSteps_spec hd a j is s₁ P _ (fun i hi => (hc i (by omega)).of_only o₁ (by decide)) v₁ ?_
      fun s₂ o₂ v₂ => k s₂ ((o₁.trans o₂).mono fun r hr => by
        rcases List.mem_append.mp hr with h | h <;> exact h) ?_
    · have hc' := VG.Proof.MlKem.X86.cf_lt d (a j)
      have : A * 2 ^ d + VG.Proof.MlKem.X86.cf d (a j) + 1 ≤ (A + 1) * 2 ^ d := by rw [Nat.add_mul]; omega
      refine Nat.le_trans (Nat.mul_le_mul_right _ this) ?_
      rw [Nat.mul_assoc, ← hsplit]; exact hb
    · rw [v₂, VG.Proof.MlKem.X86.pk, hsplit, Nat.add_mul, Nat.mul_assoc]
      omega

theorem pk_congr {d : Nat} {cv cv' : Nat → Nat} : ∀ {j : Nat}, (∀ i < j, cv i = cv' i) →
    VG.Proof.MlKem.X86.pk d cv j = VG.Proof.MlKem.X86.pk d cv' j
  | 0, _ => rfl
  | j + 1, h => by rw [VG.Proof.MlKem.X86.pk, VG.Proof.MlKem.X86.pk, VG.Proof.MlKem.X86.pk_congr (fun i hi => h i (by omega)), h j (by omega)]

theorem pk_lt {d : Nat} (cv : Nat → Nat) (h : ∀ i, cv i < 2 ^ d) : ∀ j, VG.Proof.MlKem.X86.pk d cv j < 2 ^ (d * j)
  | 0 => by simp [VG.Proof.MlKem.X86.pk]
  | j + 1 => by
    have ih := VG.Proof.MlKem.X86.pk_lt cv h j
    have hc := h j
    have e : 2 ^ (d * (j + 1)) = 2 ^ d * 2 ^ (d * j) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ, Nat.add_comm]
    rw [VG.Proof.MlKem.X86.pk, e]
    have : cv j * 2 ^ (d * j) + 2 ^ (d * j) ≤ 2 ^ d * 2 ^ (d * j) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hc
    omega

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.CompressEncode`. -/
section

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_compress_encode`

The branch on `d` depends only on `d`; each branch is a loop over groups of
coefficients, packed with `accSteps` (`Pack.lean`) into the bytes of
`compressEncode1`, `compressEncode4` and `compressEncode10_*` (`Encode.lean`).
-/

namespace VG.Proof.MlKem.X86.CompressEncode

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev dV : BitVec 32 := arg s₀ 1
abbrev oP : BitVec 32 := arg s₀ 2
abbrev lenV : BitVec 32 := arg s₀ 3
abbrev fA : Addr := (VG.Proof.MlKem.X86.CompressEncode.fP s₀).setWidth 64
abbrev oA : Addr := (VG.Proof.MlKem.X86.CompressEncode.oP s₀).setWidth 64
abbrev oR : Region := ⟨VG.Proof.MlKem.X86.CompressEncode.oA s₀, (VG.Proof.MlKem.X86.CompressEncode.lenV s₀).toNat⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev dN : Nat := (VG.Proof.MlKem.X86.CompressEncode.dV s₀).toNat
/-- The encoding. -/
abbrev L : List Byte := compressEncode (VG.Proof.MlKem.X86.CompressEncode.dN s₀) (polyAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀))
/-- Compressed coefficient `i`. -/
abbrev C (i : Nat) : Nat := compress (VG.Proof.MlKem.X86.CompressEncode.dN s₀) (polyAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀))[i]!
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀)]
  wr : s₀.wr = [VG.Proof.MlKem.X86.CompressEncode.oR s₀, VG.Proof.MlKem.X86.CompressEncode.aR s₀]
  f_o : (polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀)).Disjoint (VG.Proof.MlKem.X86.CompressEncode.oR s₀)
  f_a : (polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀)).Disjoint (VG.Proof.MlKem.X86.CompressEncode.aR s₀)
  o_a : (VG.Proof.MlKem.X86.CompressEncode.oR s₀).Disjoint (VG.Proof.MlKem.X86.CompressEncode.aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀))
  ret_o : (retR s₀).Disjoint (VG.Proof.MlKem.X86.CompressEncode.oR s₀)
  ret_a : (retR s₀).Disjoint (VG.Proof.MlKem.X86.CompressEncode.aR s₀)
  stk_f : (VG.Proof.MlKem.X86.CompressEncode.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀))
  stk_o : (VG.Proof.MlKem.X86.CompressEncode.stkR s₀).Disjoint (VG.Proof.MlKem.X86.CompressEncode.oR s₀)
  stk_a : (VG.Proof.MlKem.X86.CompressEncode.stkR s₀).Disjoint (VG.Proof.MlKem.X86.CompressEncode.aR s₀)
  f_fit : (VG.Proof.MlKem.X86.CompressEncode.fP s₀).toNat + 1024 ≤ 2 ^ 32
  o_fit : (VG.Proof.MlKem.X86.CompressEncode.oP s₀).toNat + (VG.Proof.MlKem.X86.CompressEncode.lenV s₀).toNat ≤ 2 ^ 32
  d_mem : VG.Proof.MlKem.X86.CompressEncode.dN s₀ ∈ compressWidths
  len_eq : (VG.Proof.MlKem.X86.CompressEncode.lenV s₀).toNat = 32 * VG.Proof.MlKem.X86.CompressEncode.dN s₀
  f_red : Reduced s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀)

theorem Pre.of {s₀ : State} (h : (compressEncodeContract X86.abi 16).pre s₀) : VG.Proof.MlKem.X86.CompressEncode.Pre s₀ := by
  sig_pre [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlKem.X86.CompressEncode.Pre s₀)
include hp

theorem stk_eq : VG.Proof.MlKem.X86.CompressEncode.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlKem.X86.CompressEncode.stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem f_keep {s : State} (hf : Frame [VG.Proof.MlKem.X86.CompressEncode.oR s₀] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) i = coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) i := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  refine coeffAt_congr (fun j hj => ?_) hi
  rw [hf.bytes (R := polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀)) (by simpa using hp.f_o) (polyLen _) hj,
    hf₁.bytes (R := polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀)) (by simpa [← hp.stk_eq] using hp.stk_f.symm) (polyLen _) hj]

/-- `C i` from what the coefficient holds in memory. -/
theorem C_eq {i : Nat} (hi : i < 256) :
    VG.Proof.MlKem.X86.CompressEncode.C s₀ i = VG.Proof.MlKem.X86.cf (VG.Proof.MlKem.X86.CompressEncode.dN s₀) (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) i).toNat := by
  rw [VG.Proof.MlKem.X86.cf_eq hp.d_mem (hp.f_red i hi), VG.Proof.MlKem.X86.CompressEncode.C, polyAt_get _ _ hi]

end Pre

/-- After `t` groups of `c` coefficients and `b` bytes, counting down from `N`. -/
structure Inv (s₀ : State) (c b N t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlKem.X86.CompressEncode.fP s₀ + BitVec.ofNat 32 (4 * c * t)
  edi : s.gpr .edi = VG.Proof.MlKem.X86.CompressEncode.oP s₀ + BitVec.ofNat 32 (b * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (N - t)
  frame : Frame [VG.Proof.MlKem.X86.CompressEncode.oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < b * t, s.mem (VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 j) = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[j]!

/-- The end of every branch. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [VG.Proof.MlKem.X86.CompressEncode.oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < 32 * VG.Proof.MlKem.X86.CompressEncode.dN s₀, s.mem (VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 j) = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[j]!

theorem Inv.fin {s₀ s : State} {c b N : Nat} (hN : b * N = 32 * VG.Proof.MlKem.X86.CompressEncode.dN s₀) (h : VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N N s) :
    VG.Proof.MlKem.X86.CompressEncode.Fin s₀ s := ⟨h.esp, h.rd, h.wr, h.frame, fun j hj => h.out j (by rw [hN]; exact hj)⟩

/-- Coefficient `c t + i` of group `t`, read from `esi`. -/
theorem coef_at {s₀ s : State} (hp : VG.Proof.MlKem.X86.CompressEncode.Pre s₀) {c b N t : Nat} (h : VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N t s) {i : Nat}
    (hi : c * t + i < 256) :
    VG.Proof.MlKem.X86.Coef s i (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (c * t + i)).toNat := by
  have ff := hp.f_fit
  have e : s.ea (at_ .esi (4 * i)) = coeffAddr (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (c * t + i) := by
    show (s.gpr .esi + BitVec.ofNat 32 (4 * i)).setWidth 64 = _
    rw [h.esi, ea_add (by rw [show 4 * c * t = 4 * (c * t) from Nat.mul_assoc 4 c t]; omega)]
    congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  refine ⟨?_, ?_, hp.f_red _ (by rw [n_eq]; exact hi)⟩
  · rw [e]; exact ⟨polyRegion (VG.Proof.MlKem.X86.CompressEncode.fA s₀), by rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]; simp,
      coeff_contains _ (by rw [n_eq]; exact hi)⟩
  · rw [e, ← coeffAt_eq, hp.f_keep h.frame hi]

/-- Store a byte of `ebx`/`eax` at `edi + o`: in the output region. -/
theorem out_in {s₀ s : State} (hp : VG.Proof.MlKem.X86.CompressEncode.Pre s₀) (hw : s.wr = (P0 s₀).wr) {j : Nat}
    (hj : j < (VG.Proof.MlKem.X86.CompressEncode.lenV s₀).toNat) : InRegions s.wr (VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 j) 1 :=
  ⟨VG.Proof.MlKem.X86.CompressEncode.oR s₀, by rw [hw, P0_wr, hp.wr]; simp, contains_at (by omega) hp.o_fit⟩

/-! ## `d` = 1 and 4: a byte of `k` coefficients -/

theorem byte14 {s₀ : State} {d k : Nat} (hd : VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d) (hdk : d * k = 8)
    (hd14 : d = 1 ∨ d = 4) {t : Nat} (ht : t < 32 * d) :
    (VG.Proof.MlKem.X86.CompressEncode.L s₀)[t]! = BitVec.ofNat 8 (VG.Proof.MlKem.X86.pk d (fun i => VG.Proof.MlKem.X86.CompressEncode.C s₀ (k * t + i)) k) := by
  rcases hd14 with rfl | rfl
  · have hk : k = 8 := by omega
    subst hk
    rw [VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode1 _ (by omega)]
    simp only [VG.Proof.MlKem.X86.pk, VG.Proof.MlKem.X86.CompressEncode.C, hd]
    refine congrArg (BitVec.ofNat 8) ?_
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
    omega
  · have hk : k = 2 := by omega
    subst hk
    rw [VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode4 _ (by omega)]
    simp only [VG.Proof.MlKem.X86.pk, VG.Proof.MlKem.X86.CompressEncode.C, hd]
    refine congrArg (BitVec.ofNat 8) ?_
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
    omega

theorem step14 {s₀ : State} (hp : VG.Proof.MlKem.X86.CompressEncode.Pre s₀) {d k N : Nat} (hd : VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d) (hdk : d * k = 8)
    (hd14 : d = 1 ∨ d = 4) (hN : N = 32 * d) {t : Nat} (ht : t < N) {s : State}
    (h : VG.Proof.MlKem.X86.CompressEncode.Inv s₀ k 1 N t s) :
    WP isa (.block (packBody d k)) s fun s' => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ k 1 N (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < N)) := by
  have hdm : d ∈ compressWidths := hd ▸ hp.d_mem
  have hk1 : 1 ≤ k := by rcases hd14 with rfl | rfl <;> omega
  have hkt : k * t + k ≤ 256 := by
    rcases hd14 with rfl | rfl
    · have : k = 8 := by omega
      subst this; omega
    · have : k = 2 := by omega
      subst this; omega
  have fo := hp.o_fit
  have hl := hp.len_eq
  have hC : ∀ i < k, VG.Proof.MlKem.X86.CompressEncode.C s₀ (k * t + i) = VG.Proof.MlKem.X86.cf d (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (k * t + i)).toNat := fun i hi => by
    rw [hp.C_eq (by omega), hd]
  refine VG.Proof.MlKem.X86.ldComp_spec hdm (k - 1) _ s _ (VG.Proof.MlKem.X86.CompressEncode.coef_at hp h (i := k - 1) (by omega)) fun s₁ o₁ v₁ => ?_
  refine wp_movr ?_
  have o₂ := o₁.trans (Only.setReg s₁ .ebx (s₁.gpr .eax))
  have bx : ((s₁.setReg .ebx (s₁.gpr .eax)).gpr .ebx).toNat = VG.Proof.MlKem.X86.cf d (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (k * t + (k - 1))).toNat := by
    simp only [State.setReg, ite_true]; exact v₁
  refine VG.Proof.MlKem.X86.accSteps_spec hdm (fun i => (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (k * t + i)).toNat) (k - 1) _ _ _ _
    (fun i hi => (VG.Proof.MlKem.X86.CompressEncode.coef_at hp h (i := i) (by omega)).of_only o₂ (by decide)) bx ?_ fun s₃ o₃ v₃ => ?_
  · have := VG.Proof.MlKem.X86.cf_lt d (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (k * t + (k - 1))).toNat
    calc _ ≤ 2 ^ d * 2 ^ (d * (k - 1)) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 8 := by rw [← Nat.pow_add]; congr 1; rw [← hdk]; rcases hd14 with rfl | rfl <;> omega
      _ ≤ 2 ^ 32 := by decide
  have o := o₂.trans o₃
  have g : ∀ r, r ∉ [Reg.eax, .edx, .ebx] → s₃.gpr r = s.gpr r := fun r hr =>
    o.gpr r (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      simp only [hr, not_false_eq_true, and_self])
  have esi₃ := g .esi (by decide)
  have edi₃ := g .edi (by decide)
  have ecx₃ := g .ecx (by decide)
  have esp₃ := g .esp (by decide)
  have eo : (VG.Proof.MlKem.X86.CompressEncode.oP s₀ + BitVec.ofNat 32 t + BitVec.ofNat 32 0).setWidth 64 = VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 t := by
    rw [ea_add (by omega), Nat.add_zero]
  have out := VG.Proof.MlKem.X86.CompressEncode.out_in hp (o.wr.trans h.wr) (j := t) (by omega)
  have ho : 1 * t = t := Nat.one_mul t
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store8, State.setReg, arithFlags, State.setFlags, Reg8.reg,
    Option.bind_some, edi₃, h.edi, ho, eo, out, Option.some.injEq, exists_eq_left']
  have hbyte : (s₃.gpr .ebx).setWidth 8 = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[t]! := by
    rw [setWidth8_eq, v₃, VG.Proof.MlKem.X86.CompressEncode.byte14 hd hdk hd14 (by omega), VG.Proof.MlKem.X86.pk_congr (fun i hi => hC i hi)]
    refine congrArg (BitVec.ofNat 8) ?_
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [VG.Proof.MlKem.X86.pk, Nat.add_sub_cancel]
    omega
  refine ⟨⟨by simp [esp₃, h.esp], o.rd.trans h.rd, o.wr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true,
      esi₃, h.esi]
    rw [add_ofNat_add]; congr 2
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, edi₃, h.edi]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2; omega
  · simp only [ite_true, ecx₃, h.ecx]
    exact cnt_next ht
  · rw [o.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_at (by omega) fo)
  · rw [o.mem, show 1 * (t + 1) = t + 1 by omega]
    exact bytes_extend1 (by omega) (fun j hj => h.out j (by omega)) hbyte
  · simp only [eval, ecx₃, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## `d` = 10: five bytes of four coefficients -/

theorem step10 {s₀ : State} (hp : VG.Proof.MlKem.X86.CompressEncode.Pre s₀) (hd : VG.Proof.MlKem.X86.CompressEncode.dN s₀ = 10) {t : Nat} (ht : t < 64) {s : State}
    (h : VG.Proof.MlKem.X86.CompressEncode.Inv s₀ 4 5 64 t s) :
    WP isa (.block pack10Body) s fun s' => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ 4 5 64 (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < 64)) := by
  have hdm : (10 : Nat) ∈ compressWidths := hd ▸ hp.d_mem
  have fo := hp.o_fit
  have hl := hp.len_eq
  rw [hd] at hl
  have hC : ∀ i < 4, VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + i) = VG.Proof.MlKem.X86.cf 10 (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (4 * t + i)).toNat := fun i hi => by
    rw [hp.C_eq (by omega), hd]
  refine VG.Proof.MlKem.X86.ldComp_spec hdm 3 _ s _ (VG.Proof.MlKem.X86.CompressEncode.coef_at hp h (i := 3) (by omega)) fun s₁ o₁ v₁ => ?_
  refine wp_movr (wp_movr (wp_and fun s₂ o₂ v₂ => ?_))
  have o₃ := (o₁.trans ((Only.setReg s₁ .ebp (s₁.gpr .eax)).trans (Only.setReg _ .ebx _))).trans o₂
  have bx : (s₂.gpr .ebx).toNat = VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 3) % 4 := by
    rw [v₂, show (3 : BitVec 32) = BitVec.ofNat 32 (2 ^ 2 - 1) from rfl, toNat_and_mask _ _ (by decide)]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, State.setReg]
    rw [v₁, hC 3 (by omega)]
  have bp : s₂.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 3)) := by
    rw [o₂.gpr .ebp (by decide)]
    simp only [State.setReg, ite_true, show Reg.ebp ≠ Reg.ebx by decide, ite_false]
    rw [eq_ofNat_of_toNat v₁, hC 3 (by omega)]
  refine VG.Proof.MlKem.X86.accSteps_spec hdm (fun i => (coeffAt s₀.mem (VG.Proof.MlKem.X86.CompressEncode.fA s₀) (4 * t + i)).toNat) 3 _ _ _ _
    (fun i hi => (VG.Proof.MlKem.X86.CompressEncode.coef_at hp h (i := i) (by omega)).of_only o₃ (by decide)) bx
    (by have := Nat.mod_lt (VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 3)) (show 4 > 0 by decide); omega) fun s₄ o₄ v₄ => ?_
  have o := o₃.trans o₄
  have g : ∀ r, r ∉ [Reg.eax, .edx, .ebx, .ebp] → s₄.gpr r = s.gpr r := fun r hr =>
    o.gpr r (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      simp only [hr, not_false_eq_true, and_self])
  have esi₄ := g .esi (by decide)
  have edi₄ := g .edi (by decide)
  have ecx₄ := g .ecx (by decide)
  have esp₄ := g .esp (by decide)
  have bp₄ : s₄.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 3)) := by rw [o₄.gpr .ebp (by decide), bp]
  have eo : ∀ j < 5, (VG.Proof.MlKem.X86.CompressEncode.oP s₀ + BitVec.ofNat 32 (5 * t) + BitVec.ofNat 32 j).setWidth 64 =
      VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 (5 * t + j) := fun j hj => ea_add (by omega)
  have e0 := eo 0 (by omega)
  have e1 := eo 1 (by omega)
  have e2 := eo 2 (by omega)
  have e3 := eo 3 (by omega)
  have e4 := eo 4 (by omega)
  have wr := o.wr.trans h.wr
  have out : ∀ j < 5, InRegions s₄.wr (VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 (5 * t + j)) 1 :=
    fun j hj => VG.Proof.MlKem.X86.CompressEncode.out_in hp wr (by omega)
  have w0 := out 0 (by omega)
  have w1 := out 1 (by omega)
  have w2 := out 2 (by omega)
  have w3 := out 3 (by omega)
  have w4 := out 4 (by omega)
  simp only [Nat.add_zero] at e0 w0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.ea, at_, State.store8, State.setReg, arithFlags, State.setFlags, Reg8.reg,
    Option.bind_some, Option.map_some, edi₄, h.edi, e0, e1, e2, e3, e4, w0, w1, w2, w3, w4, bp₄,
    Option.some.injEq, exists_eq_left']
  -- The values.
  have lc : ∀ i < 4, VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + i) < 1024 := fun i _ => by rw [VG.Proof.MlKem.X86.CompressEncode.C, hd]; exact compress_lt 10 _
  have l0 := lc 0 (by omega)
  rw [Nat.add_zero] at l0
  have l1 := lc 1 (by omega)
  have l2 := lc 2 (by omega)
  have l3 := lc 3 (by omega)
  have hW : (s₄.gpr .ebx).toNat = VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t) + 1024 * VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 1) +
      1048576 * VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 2) + 1073741824 * (VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 3) % 4) := by
    rw [v₄, VG.Proof.MlKem.X86.pk_congr (cv' := fun i => VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + i)) (fun i hi => (hC i (by omega)).symm)]
    simp only [VG.Proof.MlKem.X86.pk, Nat.add_zero]
    omega
  generalize s₄.gpr .ebx = W at hW
  have hb : ∀ j < 4, (W >>> (8 * j)).setWidth 8 = BitVec.ofNat 8 (W.toNat / 2 ^ (8 * j)) := fun j _ => by
    rw [setWidth8_eq, toNat_shr]
  have x0 : W.setWidth 8 = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[5 * t]! := by
    rw [setWidth8_eq, VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode10_0 _ ht]
    exact ofNat8_eq (by simp only [VG.Proof.MlKem.X86.CompressEncode.C, hd] at hW l0 l1 l2 l3 ⊢; omega)
  have x1 : (W >>> 8).setWidth 8 = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[5 * t + 1]! := by
    rw [setWidth8_eq, toNat_shr, VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode10_1 _ ht]
    exact ofNat8_eq (by simp only [VG.Proof.MlKem.X86.CompressEncode.C, hd, Nat.reducePow] at hW l0 l1 l2 l3 ⊢; omega)
  have x2 : (W >>> 8 >>> 8).setWidth 8 = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[5 * t + 2]! := by
    rw [setWidth8_eq, toNat_shr, toNat_shr, VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode10_2 _ ht]
    exact ofNat8_eq (by simp only [VG.Proof.MlKem.X86.CompressEncode.C, hd, Nat.reducePow] at hW l0 l1 l2 l3 ⊢; omega)
  have x3 : (W >>> 8 >>> 8 >>> 8).setWidth 8 = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[5 * t + 3]! := by
    rw [setWidth8_eq, toNat_shr, toNat_shr, toNat_shr, VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode10_3 _ ht]
    exact ofNat8_eq (by simp only [VG.Proof.MlKem.X86.CompressEncode.C, hd, Nat.reducePow] at hW l0 l1 l2 l3 ⊢; omega)
  have x4 : (BitVec.ofNat 32 (VG.Proof.MlKem.X86.CompressEncode.C s₀ (4 * t + 3)) >>> 2).setWidth 8 = (VG.Proof.MlKem.X86.CompressEncode.L s₀)[5 * t + 4]! := by
    rw [setWidth8_eq, toNat_shr, toNat_ofNat32 (by omega), VG.Proof.MlKem.X86.CompressEncode.L, hd, compressEncode10_4 _ ht]
    simp only [VG.Proof.MlKem.X86.CompressEncode.C, hd]
  clear hb
  refine ⟨⟨by simp [esp₄, h.esp], o.rd.trans h.rd, wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true,
      esi₄, h.esi]
    rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]; congr 2
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, edi₄, h.edi]
    rw [show (5 : BitVec 32) = BitVec.ofNat 32 5 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, ecx₄, h.ecx]
    exact cnt_next ht
  · rw [o.mem]
    have c : ∀ j < 5, (VG.Proof.MlKem.X86.CompressEncode.oR s₀).Contains (VG.Proof.MlKem.X86.CompressEncode.oA s₀ + BitVec.ofNat 64 (5 * t + j)) (8 / 8) :=
      fun j hj => contains_at (by omega) fo
    have c0 := c 0 (by omega)
    simp only [Nat.add_zero] at c0
    exact ((((h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _
      (c 1 (by omega))).writeW (List.mem_singleton_self _) _ (c 2 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 3 (by omega))).writeW (List.mem_singleton_self _) _ (c 4 (by omega))
  · rw [o.mem, show 5 * (t + 1) = 5 * t + 4 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x4
    rw [show 5 * t + 4 = 5 * t + 3 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x3
    rw [show 5 * t + 3 = 5 * t + 2 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x2
    rw [show 5 * t + 2 = 5 * t + 1 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x1
    exact bytes_extend1 (by omega) h.out x0
  · simp only [eval, ecx₄, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## The function -/

/-- After `ceInit`, or the compare with `v`. -/
structure Init (s₀ : State) (v : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = VG.Proof.MlKem.X86.CompressEncode.fP s₀
  edi : s.gpr .edi = VG.Proof.MlKem.X86.CompressEncode.oP s₀
  eax : s.gpr .eax = VG.Proof.MlKem.X86.CompressEncode.dV s₀
  ev : eval .e s = some (decide (VG.Proof.MlKem.X86.CompressEncode.dN s₀ = v))

theorem pub_esp {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.CompressEncode.Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

theorem init_piece : Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => s = P0 s₀) (VG.Proof.MlKem.X86.CompressEncode.Init · 1) (.block ceInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₁ := P0_argAddr s₀ 1
    have a₂ := P0_argAddr s₀ 2
    have i₀ := P0_argIn (s₀ := s₀) (n := 4) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₁ := P0_argIn (s₀ := s₀) (n := 4) (i := 1) (by omega) fit (by simp [hp.wr])
    have i₂ := P0_argIn (s₀ := s₀) (n := 4) (i := 2) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 4) (i := 0) (by omega) fit hp.stk_a
    have v₁ := P0_arg hp.sp (n := 4) (i := 1) (by omega) fit hp.stk_a
    have v₂ := P0_arg hp.sp (n := 4) (i := 2) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, ceInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, by simp, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', VG.Proof.MlKem.X86.CompressEncode.pub_esp hq]

theorem cmp4_piece : Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => VG.Proof.MlKem.X86.CompressEncode.Init s₀ 1 s ∧ decide (VG.Proof.MlKem.X86.CompressEncode.dN s₀ = 1) = false)
    (fun s₀ s => VG.Proof.MlKem.X86.CompressEncode.Init s₀ 4 s ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ ≠ 1) (.block [.alu .cmp .eax (.imm 4)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, h1⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.esp, h.rd, h.wr, h.mem, h.esi, h.edi, h.eax, ?_⟩, of_decide_eq_false h1⟩
  simp only [eval, sub_beq_zero, h.eax]
  rfl

theorem ecx_piece (d c b N : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) hc).isSome = true) :
    Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => (∃ v, VG.Proof.MlKem.X86.CompressEncode.Init s₀ v s) ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d)
      (fun s₀ s => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N 0 s ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨v, h⟩, hd⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    ht
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp [h.edi], by simp,
    (by rw [h.mem]; exact Frame.refl _ _), fun j hj => absurd hj (by omega)⟩, hd⟩

theorem loop_piece {d c b N : Nat} (body : List Instr) (hN : 0 < N)
    (hstep : ∀ t < N, ∀ s₀ s, VG.Proof.MlKem.X86.CompressEncode.Pre s₀ → VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d → VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N t s →
      WP isa (.block body) s fun s' => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < N)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true) :
    Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N 0 s ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d) (fun s₀ s => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N N s ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d)
      (.loop (.block body) .ne) :=
  Piece.countLoop hN (fun t s₀ s => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N t s ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d) [.esp, .esi, .edi, .ecx]
    (fun t ht s₀ s hp ⟨h, hd⟩ => (hstep t ht s₀ s hp hd h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hd⟩, e⟩)
    (fun t _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, VG.Proof.MlKem.X86.CompressEncode.pub_esp hq]
      · rw [h.esi, h'.esi, VG.Proof.MlKem.X86.CompressEncode.fP, VG.Proof.MlKem.X86.CompressEncode.fP, hq.2.1]
      · rw [h.edi, h'.edi, VG.Proof.MlKem.X86.CompressEncode.oP, VG.Proof.MlKem.X86.CompressEncode.oP, hq.2.2.2.1]
      · rw [h.ecx, h'.ecx]) ht

theorem branch_piece {d c b N : Nat} (body : List Instr) (hN : 0 < N) (hbN : b * N = 32 * d)
    (hstep : ∀ t < N, ∀ s₀ s, VG.Proof.MlKem.X86.CompressEncode.Pre s₀ → VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d → VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N t s →
      WP isa (.block body) s fun s' => VG.Proof.MlKem.X86.CompressEncode.Inv s₀ c b N (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < N)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true)
    {hc' : Taint.Hint VG.X86.Taint.T}
    (ht' : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) hc').isSome = true) :
    Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => (∃ v, VG.Proof.MlKem.X86.CompressEncode.Init s₀ v s) ∧ VG.Proof.MlKem.X86.CompressEncode.dN s₀ = d) VG.Proof.MlKem.X86.CompressEncode.Fin (countedLoop N body) :=
  (Piece.seq (VG.Proof.MlKem.X86.CompressEncode.ecx_piece d c b N ht') (VG.Proof.MlKem.X86.CompressEncode.loop_piece body hN hstep ht)).mono (fun _ _ _ h => h)
    fun _ _ _ ⟨h, hd⟩ => h.fin (by rw [hd, hbN])

theorem ite_ev {v : Nat} {P : State → State → Prop} :
    ∀ s₀ s, VG.Proof.MlKem.X86.CompressEncode.Pre s₀ → VG.Proof.MlKem.X86.CompressEncode.Init s₀ v s ∧ P s₀ s → eval .e s = some (decide (VG.Proof.MlKem.X86.CompressEncode.dN s₀ = v)) :=
  fun _ _ _ h => h.1.ev

theorem ite_pub (v : Nat) : ∀ s₀ s₀', VG.Proof.MlKem.X86.CompressEncode.Pre s₀ → VG.Proof.MlKem.X86.CompressEncode.Pre s₀' → VG.Proof.MlKem.X86.CompressEncode.Pub s₀ s₀' →
    decide (VG.Proof.MlKem.X86.CompressEncode.dN s₀ = v) = decide (VG.Proof.MlKem.X86.CompressEncode.dN s₀' = v) := fun _ _ _ _ hq => by rw [VG.Proof.MlKem.X86.CompressEncode.dN, VG.Proof.MlKem.X86.CompressEncode.dN, VG.Proof.MlKem.X86.CompressEncode.dV, VG.Proof.MlKem.X86.CompressEncode.dV, hq.2.2.1]

theorem body_piece : Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem.X86.CompressEncode.Fin
    (.seq (.block ceInit)
      (.ite .e (countedLoop 32 (packBody 1 8))
        (.seq (.block [.alu .cmp .eax (.imm 4)])
          (.ite .e (countedLoop 128 (packBody 4 2)) (countedLoop 64 pack10Body))))) := by
  refine Piece.seq (init_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h, trivial⟩)
    (Piece.ite _ (VG.Proof.MlKem.X86.CompressEncode.ite_ev (P := fun _ _ => True)) (VG.Proof.MlKem.X86.CompressEncode.ite_pub 1) ?_ ?_)
  · exact (VG.Proof.MlKem.X86.CompressEncode.branch_piece (d := 1) (c := 8) (b := 1) (packBody 1 8) (by decide) rfl
      (fun t ht s₀ s hp hd h => VG.Proof.MlKem.X86.CompressEncode.step14 hp hd (by decide) (.inl rfl) rfl ht h) (by taint_decide) (by taint_decide)).mono
      (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨⟨1, h⟩, of_decide_eq_true e⟩) fun _ _ _ h => h
  refine Piece.seq (cmp4_piece.mono (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨h, e⟩) fun _ _ _ h => h)
    (Piece.ite _ VG.Proof.MlKem.X86.CompressEncode.ite_ev (VG.Proof.MlKem.X86.CompressEncode.ite_pub 4) ?_ ?_)
  · exact (VG.Proof.MlKem.X86.CompressEncode.branch_piece (d := 4) (c := 2) (b := 1) (packBody 4 2) (by decide) rfl
      (fun t ht s₀ s hp hd h => VG.Proof.MlKem.X86.CompressEncode.step14 hp hd (by decide) (.inr rfl) rfl ht h) (by taint_decide) (by taint_decide)).mono
      (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨⟨4, h⟩, of_decide_eq_true e⟩) fun _ _ _ h => h
  · exact (VG.Proof.MlKem.X86.CompressEncode.branch_piece (d := 10) (c := 4) (b := 5) pack10Body (by decide) rfl
      (fun t ht s₀ s hp hd h => VG.Proof.MlKem.X86.CompressEncode.step10 hp hd ht h) (by taint_decide) (by taint_decide)).mono
      (fun s₀ _ hp ⟨⟨h, h1⟩, e⟩ => ⟨⟨4, h⟩, by
        have := hp.d_mem
        have h4 := of_decide_eq_false e
        rcases mem_compressWidths this with h' | h' | h' <;> [exact absurd h' h1; exact absurd h' h4; exact h']⟩)
      fun _ _ _ h => h

theorem piece : Piece VG.Proof.MlKem.X86.CompressEncode.Pre VG.Proof.MlKem.X86.CompressEncode.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.CompressEncode.Fin s₀) s₀ s')
    Impl.MlKem.X86.compressEncode :=
  Piece.leaf (fun s₀ => [VG.Proof.MlKem.X86.CompressEncode.oR s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_o, hp.ret_o⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `1`, `0x400` and `32` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 1 else if a = 0x500d then 4 else if a = 0x5010 then 32 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.compressEncode (compressEncodeContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := Pre.of h₀
    rw [hm, hp.len_eq]
    exact bytesAt_eq! (compressEncode_length _ _) fun j hj => hinv.out j hj
  · let st := satState VG.Proof.MlKem.X86.CompressEncode.satMem [⟨0, 1024⟩] [⟨0x400, 32⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 1 := by decide
    have a2 : arg st 2 = 0x400 := by decide
    have a3 : arg st 3 = 32 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      by decide, by decide, reduced_below (fun a ha => ?_) 0 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show VG.Proof.MlKem.X86.CompressEncode.satMem a = 0
         simp only [VG.Proof.MlKem.X86.CompressEncode.satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])

end VG.Proof.MlKem.X86.CompressEncode

end
