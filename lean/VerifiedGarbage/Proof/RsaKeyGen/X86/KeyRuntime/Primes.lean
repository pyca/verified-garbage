module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Product
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `RsaKeyGen.X86.KeyRuntime.PrimeProduct`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.Product`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.ProductLayout`, which only this module used -/

section

/-! # Layout of the native unreduced RSA product

The operands may coincide (squaring is permitted). The product and the
multiplier word cannot overlap either operand or each other.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.Proof.Mont

structure Layout (size left right out a b mult : Nat) : Prop where
  left_pos : 0 < left
  right_pos : 0 < right
  right_even : right % 2 = 0
  out_bound : out + 4 * (left + right + 2) ≤ size
  a_bound : a + 4 * left ≤ size
  b_bound : b + 4 * right ≤ size
  mult_bound : mult + 4 ≤ size
  a_out : a + 4 * left ≤ out ∨ out + 4 * (left + right + 2) ≤ a
  b_out : b + 4 * right ≤ out ∨ out + 4 * (left + right + 2) ≤ b
  mult_out : mult + 4 ≤ out ∨ out + 4 * (left + right + 2) ≤ mult
  a_mult : a + 4 * left ≤ mult ∨ mult + 4 ≤ a
  b_mult : b + 4 * right ≤ mult ∨ mult + 4 ≤ b

end VG.Proof.RsaKeyGen.X86.Product

end

end

/-! # The product at the run-time width: a row of `b` for each word of `a` -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ProductGeometry.lean`, which only this module imported.
section

/-! # Geometry and public cursors of the shared native product -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont

structure ProductGeometry (Z left right out a b : Nat) : Prop extends
    VG.Proof.RsaKeyGen.X86.Product.Layout Z left right out a b 128 where
  a_header : 156 ≤ a
  b_header : 156 ≤ b
  out_header : 156 ≤ out

def productRanges (left right out : Nat) : List (Nat × Nat) :=
  [(128, 28), (out, 4 * (left + right + 2))]


end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt

section
variable {s : State} {B : Addr} {Z n N : Nat}

theorem Ws.edi_at (h : Ws s B Z n N) : PtrAt s B .edi 0 := by
  have := h.old.workspace.nowrap
  have head := h.hdr_le
  unfold VG.Impl.Rsa.X86.Keys.hdr at head
  rw [PtrAt, h.old.workspace.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [this, head])]

/-- The `left + right + 2` words of `out` zeroed. -/
theorem productZero_ok (h : Ws s B Z n N) (left right : Width) (out : Loc)
    (fit : out.offset n + 4 * (left.words n + right.words n + 2) ≤ Z) :
    WP isa (productZero left right out) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * (left.words n + right.words n + 2)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (left.words n + right.words n + 2) = 0 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  have nBound := h.old.wle
  have wBound (w : Width) : w.words n ≤ 1024 := by
    cases w <;> simp only [Width.words] <;> omega_arith
  obtain lb := wBound left
  obtain rb := wBound right
  unfold productZero
  simp only [List.append_assoc]
  refine WP.seq (h.ptr_ok out (by decide) (by decide) (by omega_using [fit, nowrap]) fun u K1 m1 P1 => ?_)
  obtain hu := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine hu.bytes_ok left .ecx fun v K2 m2 cl => ?_
  obtain hv := hu.keep K2 (by rw [m2]; exact Outside.refl _ _ _ _)
  refine hv.bytes_ok right .eax fun w K3 m3 cr => ?_
  refine wp_addS rfl fun a A _ => wp_addS rfl fun b Bb _ => wp_movS rfl fun c U _ => WP.block_nil ?_
  obtain K : Keeps [.eax, .ecx, .edx, .ebp] s c :=
    (((K1.mono (by decide)).trans (K2.mono (by decide))).trans (K3.mono (by decide))).trans
      (((A.keeps.mono (by decide)).trans (Bb.keeps.mono (by decide))).trans (U.keeps.mono (by decide)))
  obtain m : c.mem = s.mem := by rw [U.mem, Bb.mem, A.mem, m3, m2, m1]
  obtain pointer : PtrAt c B .ebp (out.offset n) := by
    rw [PtrAt, U.other _ (by decide), Bb.other _ (by decide), A.other _ (by decide), K3.1 _ (by decide),
      K2.1 _ (by decide)]
    exact P1
  obtain ecx : (c.gpr .ecx).toNat = 4 * (left.words n + right.words n + 2) := by
    rw [U.other _ (by decide), Bb.gpr, A.gpr, BitVec.toNat_add, BitVec.toNat_add, cr, K3.1 _ (by decide), cl]
    change ((4 * left.words n + 4 * right.words n) % 2 ^ 32 + 8) % 2 ^ 32 = _
    omega_using [lb, rb]
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.full.rt.of_keeps K)
    (by omega_using [] : 0 < left.words n + right.words n + 2) fit pointer ecx U.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  obtain allK := K.trans (Kt.mono (by decide))
  exact ⟨h.keep allK (O.mono (Nat.zero_le _) (by omega_using [fit])), O, V, allK⟩

/-- Row `i`'s multiplier, word `i` of `a`, in the header, `ecx` at `b`, `esi` its bytes and no carry. -/
theorem productRow_ok (h : Ws s B Z n N) (right : Width) (out a b : Loc) {i : Nat}
    (fitA : a.offset n + 4 * (i + 1) ≤ Z) (fitB : b.offset n + 4 * right.words n ≤ Z) (rpos : 0 < right.words n)
    (row : out.offset n + 4 * i < Z) (P : PtrAt s B .ebp (out.offset n + 4 * i)) :
    WP isa (.block (productRow right out a b)) s fun u => Ws u B Z n N ∧
      Outside B multSlot 4 s.mem u.mem ∧ w32 u.mem B multSlot = w32 s.mem B (a.offset n + 4 * i) ∧
      PtrAt u B .ecx (b.offset n) ∧ (u.gpr .esi).toNat = 4 * right.words n ∧ u.gpr .ebx = 0 ∧
      PtrAt u B .ebp (out.offset n + 4 * i) ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s u := by
  have nowrap := h.old.workspace.nowrap
  have hb := h.hdr_le
  unfold VG.Impl.Rsa.X86.Keys.hdr at hb
  unfold productRow
  simp only [List.append_assoc]
  refine h.ptr_ok out (r := .eax) (t := .edx) (by decide) (by decide) (by omega_using [row, nowrap]) fun u1 K1 m1 P1 => ?_
  obtain h1 := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine wp_movS rfl fun u2 U2 _ => wp_subS rfl fun u3 U3 _ => ?_
  obtain K3 : Keeps [.eax, .edx, .ecx] s u3 := ((K1.mono (by decide)).trans (U2.keeps.mono (by decide))).trans
    (U3.keeps.mono (by decide))
  obtain m3 : u3.mem = s.mem := by rw [U3.mem, U2.mem, m1]
  obtain ebp3 : PtrAt u3 B .ebp (out.offset n + 4 * i) := by rw [PtrAt, K3.1 _ (by decide)]; exact P
  obtain ecx3 : (u3.gpr .ecx).toNat = 4 * i := by
    have e2 : u2.gpr .ecx = u1.gpr .ebp := U2.gpr
    obtain pe : PtrAt u1 B .ebp (out.offset n + 4 * i) := by rw [PtrAt, K1.1 _ (by decide)]; exact P
    obtain pa : (u2.gpr .eax).toNat = (B.toNat + out.offset n) % 2 ^ 32 := by rw [U2.other _ (by decide)]; exact P1
    rw [U3.gpr, BitVec.toNat_sub, e2, pa, pe]
    omega_using [fitA, nowrap]
  obtain h3 := h.keep K3 (by rw [m3]; exact Outside.refl _ _ _ _)
  refine h3.ptr_ok a (r := .eax) (t := .edx) (by decide) (by decide) (by omega_using [fitA, nowrap]) fun u4 K4 m4 P4 => ?_
  refine wp_addS rfl fun u5 U5 _ => ?_
  obtain K5 : Keeps [.eax, .edx, .ecx] s u5 := (K3.trans (K4.mono (by decide))).trans (U5.keeps.mono (by decide))
  obtain m5 : u5.mem = s.mem := by rw [U5.mem, m4, m3]
  obtain h5 := h.keep K5 (by rw [m5]; exact Outside.refl _ _ _ _)
  obtain eax5 : PtrAt u5 B .eax (a.offset n + 4 * i) := by
    rw [PtrAt, U5.gpr, ptr_add P4, K4.1 _ (by decide), ecx3]
  refine wp_movS (readSrc_ptr h5.full.rt eax5 (d := 0) (by omega_using [fitA])) fun u6 U6 _ => ?_
  obtain K6 : Keeps [.eax, .edx, .ecx] s u6 := K5.trans (U6.keeps.mono (by decide))
  obtain h6 := h.keep K6 (by rw [U6.mem, m5]; exact Outside.refl _ _ _ _)
  refine wp_storeS (ea_ptr h6.full.rt h6.edi_at (d := multSlot) (by unfold multSlot; omega_using [hb]))
    (ws_write h6.full.rt (y := 0 + multSlot) (n := 4) (by unfold multSlot; omega_using [hb])) fun u7 U7 => ?_
  obtain m7 : u7.mem = s.mem.writeW (off B multSlot) (u6.gpr .edx) := by
    rw [U7.mem, U6.mem, m5, Nat.zero_add]
  obtain O7 : Outside B multSlot 4 s.mem u7.mem := by
    rw [m7]; exact writeW32_outside _ _ _ (by unfold multSlot; omega_using [])
  obtain K7 : Keeps [.eax, .edx, .ecx] s u7 := K6.widen (U7.keeps [])
  obtain h7 := h.keep K7 (O7.mono (Nat.zero_le _) (by unfold multSlot; omega_using [hb]))
  refine h7.ptr_ok b (r := .ecx) (t := .edx) (by decide) (by decide) (by omega_using [fitB, rpos, nowrap]) fun u8 K8 m8 P8 => ?_
  obtain h8 := h7.keep K8 (by rw [m8]; exact Outside.refl _ _ _ _)
  refine h8.bytes_ok right .esi fun u9 K9 m9 e9 => ?_
  refine wp_movS rfl fun u U _ => WP.block_nil ?_
  obtain K : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u :=
    (((K7.mono (by decide)).trans (K8.mono (by decide))).trans (K9.mono (by decide))).trans (U.keeps.mono (by decide))
  obtain m : u.mem = u7.mem := by rw [U.mem, m9, m8]
  refine ⟨h.keep K (by rw [m]; exact O7.mono (Nat.zero_le _) (by unfold multSlot; omega_using [hb])), by rw [m]; exact O7,
    ?_, ?_, ?_, U.gpr, ?_, K⟩
  · rw [m, m7, w32_write_self, U6.gpr, m5, Nat.add_zero]
  · rw [PtrAt, U.other _ (by decide), K9.1 _ (by decide)]; exact P8
  · rw [U.other _ (by decide)]; exact e9
  · rw [PtrAt, K.1 _ (by decide)]; exact P

/-- The row's carry above it, `ebp` at the next row, and ZF after the last. -/
theorem productNext_ok (h : Ws s B Z n N) (left right : Width) (out : Loc) {i : Nat}
    (hi : i < left.words n) (fit : out.offset n + 4 * (left.words n + right.words n + 2) ≤ Z)
    (P : PtrAt s B .ebp (out.offset n + 4 * i + 4 * right.words n)) :
    WP isa (.block (productNext left right out)) s fun u => Ws u B Z n N ∧
      Outside B (out.offset n + 4 * (i + right.words n)) 4 s.mem u.mem ∧
      w32 u.mem B (out.offset n + 4 * (i + right.words n)) = (s.gpr .ebx).toNat ∧
      PtrAt u B .ebp (out.offset n + 4 * (i + 1)) ∧ u.zf = some (decide (i + 1 = left.words n)) ∧
      Keeps [.eax, .edx, .ebp] s u := by
  have nowrap := h.old.workspace.nowrap
  have nBound := h.old.wle
  have wBound (w : Width) : w.words n ≤ 1024 := by
    cases w <;> simp only [Width.words] <;> omega_arith
  obtain rb := wBound right
  obtain lb := wBound left
  unfold productNext
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_storeS (ea_ptr h.full.rt P (d := 0) (by omega_using [hi, fit]))
    (ws_write h.full.rt (y := out.offset n + 4 * i + 4 * right.words n + 0) (n := 4) (by omega_using [hi, fit])) fun u1 U1 => ?_
  obtain O1 : Outside B (out.offset n + 4 * (i + right.words n)) 4 s.mem u1.mem := by
    rw [U1.mem, show out.offset n + 4 * (i + right.words n) = out.offset n + 4 * i + 4 * right.words n + 0 by omega_using []]
    exact writeW32_outside _ _ _ (by omega_using [hi, fit, nowrap])
  obtain h1 := h.keep (U1.keeps []) (O1.mono (Nat.zero_le _) (by omega_using [hi, fit]))
  refine h1.bytes_ok right .eax fun u2 K2 m2 e2 => ?_
  refine wp_subS rfl fun u3 U3 _ => wp_addS rfl fun u4 U4 _ => ?_
  obtain K4 : Keeps [.eax, .ebp] s u4 :=
    (((U1.keeps []).mono (by decide)).trans (K2.mono (by decide))).trans ((U3.keeps.trans U4.keeps).mono (by decide))
  obtain m4 : u4.mem = u1.mem := by rw [U4.mem, U3.mem, m2]
  obtain h4 := h.keep K4 (by rw [m4]; exact O1.mono (Nat.zero_le _) (by omega_using [hi, fit]))
  obtain ebp2 : PtrAt u2 B .ebp (out.offset n + 4 * i + 4 * right.words n) := by
    rw [PtrAt, K2.1 _ (by decide), U1.gpr]; exact P
  obtain ebp3 : PtrAt u3 B .ebp (out.offset n + 4 * i) := by
    rw [PtrAt, U3.gpr, ptr_sub ebp2 _ (by rw [e2]; omega_using []), e2]; congr 2; omega_using []
  obtain ebp4 : PtrAt u4 B .ebp (out.offset n + 4 * (i + 1)) := by
    rw [PtrAt, U4.gpr, ptr_add ebp3, show (4 : BitVec 32).toNat = 4 from rfl]; congr 2
  refine h4.ptr_ok out (r := .eax) (t := .edx) (by decide) (by decide) (by omega_using [fit, nowrap]) fun u5 K5 m5 P5 => ?_
  obtain h5 := h4.keep K5 (by rw [m5]; exact Outside.refl _ _ _ _)
  refine h5.bytes_ok left .edx fun u6 K6 m6 e6 => ?_
  refine wp_addS rfl fun u7 U7 _ => wp_cmpS rfl fun u F z => WP.block_nil ?_
  obtain K : Keeps [.eax, .edx, .ebp] s u :=
    (((K4.mono (by decide)).trans (K5.mono (by decide))).trans (K6.mono (by decide))).trans
      ((U7.keeps.mono (by decide)).trans (F.keeps _))
  obtain m : u.mem = u1.mem := by rw [F.mem, U7.mem, m6, m5, m4]
  obtain ebp7 : PtrAt u7 B .ebp (out.offset n + 4 * (i + 1)) := by
    rw [PtrAt, U7.other _ (by decide), K6.1 _ (by decide), K5.1 _ (by decide)]; exact ebp4
  obtain eax7 : PtrAt u7 B .eax (out.offset n + 4 * left.words n) := by
    rw [PtrAt, U7.gpr, ptr_add (x := out.offset n) (by rw [PtrAt, K6.1 _ (by decide)]; exact P5), e6]
  refine ⟨h.keep K (by rw [m]; exact O1.mono (Nat.zero_le _) (by omega_using [hi, fit])), by rw [m]; exact O1, ?_,
    by rw [PtrAt, F.gpr]; exact ebp7, ?_, K⟩
  · rw [m, U1.mem, show out.offset n + 4 * (i + right.words n) = out.offset n + 4 * i + 4 * right.words n + 0 by omega_using [],
      w32_write_self]
  · rw [z, VG.Proof.Bignum.X86.CrtRt.ptr_beq ebp7 eax7 (by omega_using [hi, fit, nowrap]) (by omega_using [fit, nowrap])]
    congr 1
    exact decide_eq_decide.mpr (by omega_using [])

theorem product_ok {left right : Width} {out a b : Loc} (h : Ws s B Z n N)
    (L : ProductGeometry Z (left.words n) (right.words n) (out.offset n) (a.offset n) (b.offset n)) :
    WP isa (product left right out a b) s fun t => Ws t B Z n N ∧
      Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (left.words n + right.words n + 2) =
        val32 s.mem B (a.offset n) (left.words n) * val32 s.mem B (b.offset n) (right.words n) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have nowrap := h.old.workspace.nowrap
  have lp := L.left_pos
  have rp := L.right_pos
  have ob := L.out_bound
  have ab := L.a_bound
  have bb := L.b_bound
  have ao := L.a_out
  have bo := L.b_out
  have ah := L.a_header
  have bh := L.b_header
  have oh := L.out_header
  have head := h.hdr_le
  unfold VG.Impl.Rsa.X86.Keys.hdr at head
  obtain ranges : ∀ r ∈ productRanges (left.words n) (right.words n) (out.offset n), r.1 + r.2 ≤ Z := by
    intro r mem
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> dsimp only <;> omega_arith
  have keepA {m : Mem} (O : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem m) (k : Nat)
      (hk : k ≤ left.words n) : val32 m B (a.offset n) k = val32 s.mem B (a.offset n) k :=
    O.val32 (fun r mem => by
      simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [nowrap, ab, hk])
  have keepB {m : Mem} (O : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem m) :
      val32 m B (b.offset n) (right.words n) = val32 s.mem B (b.offset n) (right.words n) :=
    O.val32 (fun r mem => by
      simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [nowrap, bb])
  let Bv := val32 s.mem B (b.offset n) (right.words n)
  unfold product
  refine WP.seq (WP.mono (productZero_ok h left right out ob) fun u1 ⟨h1, O1, Z1, K1⟩ => ?_)
  rw [← List.append_nil (ptr out .ebp .edx)]
  refine WP.seq (h1.ptr_ok out (r := .ebp) (t := .edx) (by decide) (by decide) (by omega_using [nowrap, ob])
    fun u2 K2 m2 P2 => WP.block_nil ?_)
  obtain h2 := h1.keep K2 (by rw [m2]; exact Outside.refl _ _ _ _)
  obtain O2 : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem u2.mem := by
    rw [m2]; exact Outs.of_outside O1 (by simp [productRanges])
  have Z2 := Z1
  rw [← m2, show left.words n + right.words n + 2 = right.words n + (left.words n + 2) by omega_using [], val32_append] at Z2
  obtain Zlo : val32 u2.mem B (out.offset n) (right.words n) = 0 := by omega_using [Z2]
  obtain Zhi : val32 u2.mem B (out.offset n + 4 * right.words n) (left.words n + 2) = 0 := by
    have : 0 < 2 ^ (32 * right.words n) := Nat.two_pow_pos _
    rcases Nat.eq_zero_of_add_eq_zero Z2 with ⟨_, z⟩
    exact (Nat.mul_eq_zero.mp z).resolve_left (by omega_using [this])
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop (N := left.words n) lp (fun i t =>
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧ Ws t B Z n N ∧ PtrAt t B .ebp (out.offset n + 4 * i) ∧
      Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (i + right.words n) = val32 s.mem B (a.offset n) i * Bv ∧
      val32 t.mem B (out.offset n + 4 * (i + right.words n)) (left.words n + 2 - i) = 0) ?step
    ⟨(K1.mono (by decide)).trans (K2.mono (by decide)), h2, by simpa using P2, O2,
      by simpa [val32] using Zlo, by simpa using Zhi⟩)
    fun t ⟨K, ht, _, O, V1, V2⟩ => ⟨ht, O, ?fin, K⟩
  case fin =>
    rw [show left.words n + 2 - left.words n = 2 by omega_using []] at V2
    rw [show left.words n + right.words n + 2 = (left.words n + right.words n) + 2 by omega_using [], val32_append, V1, V2,
      Nat.mul_zero, Nat.add_zero]
  rintro i t hi ⟨Kt, It, pt, Ot, V1, V2⟩
  -- The multiplier and the pointers.
  refine WP.seq (WP.mono (productRow_ok It right out a b (i := i) (by omega_using [ab, hi]) bb rp (by omega_using [ob, hi]) pt)
    fun u3 ⟨I3, O3, M3, c3, e3, b3, p3, K3⟩ => ?_)
  have edi3 := I3.edi_at
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.CrtRt.rowLoopAt_ok (mo := multSlot) I3.full.rt (S := 0)
    (bx := b.offset n) (w := out.offset n + 4 * i) (N := right.words n) rp edi3 c3 p3 e3 b3
    (by unfold multSlot; omega_using [head]) bb (by omega_using [ob, hi]) (by omega_using [bo, hi]) (.inl (by unfold multSlot; omega_using [oh])))
    fun u4 ⟨O4, V4, p4, K4⟩ => ?_)
  obtain I4 := I3.keep K4 (O4.mono (Nat.zero_le _) (by omega_using [ob, hi]))
  refine WP.mono (productNext_ok I4 left right out hi ob p4) fun u5 ⟨I5, O5, W5, p5, z5, K5⟩ =>
    ⟨⟨?_, I5, p5, ?_, ?_, ?_⟩, z5⟩
  · exact ((Kt.trans (K3.mono (by decide))).trans (K4.mono (by decide))).trans (K5.mono (by decide))
  · refine Ot.trans ((Outs.of_outside (O3.mono (o' := 128) (n' := 28) (by unfold multSlot; omega_using [])
      (by unfold multSlot; omega_using [])) (by simp [productRanges])).trans ((Outs.of_outside
      (O4.mono (o' := out.offset n) (n' := 4 * (left.words n + right.words n + 2)) (by omega_using []) (by omega_using [hi]))
      (by simp [productRanges])).trans (Outs.of_outside
      (O5.mono (o' := out.offset n) (n' := 4 * (left.words n + right.words n + 2)) (by omega_using []) (by omega_using [hi]))
      (by simp [productRanges]))))
  · -- The new row's value.
    obtain a3 : w32 u3.mem B (0 + multSlot) = w32 s.mem B (a.offset n + 4 * i) := by
      rw [Nat.zero_add, M3]
      obtain e := keepA Ot (i + 1) (by omega_using [hi])
      rw [val32_succ, val32_succ, keepA Ot i (by omega_using [hi])] at e
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel e)
    obtain b3' : val32 u3.mem B (b.offset n) (right.words n) = Bv := by
      rw [O3.val32 (.inr (by unfold multSlot; omega_using [bh])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3])]; exact keepB Ot
    obtain lo5 : val32 u5.mem B (out.offset n) i = val32 t.mem B (out.offset n) i := by
      rw [O5.val32 (.inl (by omega_using [])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3]), O4.val32 (.inl (by omega_using [])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3]),
        O3.val32 (.inr (by unfold multSlot; omega_using [oh])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3])]
    obtain w5 : val32 u5.mem B (out.offset n + 4 * i) (right.words n) =
        val32 u4.mem B (out.offset n + 4 * i) (right.words n) :=
      O5.val32 (.inl (by omega_using [])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3])
    obtain w3 : val32 u3.mem B (out.offset n + 4 * i) (right.words n) =
        val32 t.mem B (out.offset n + 4 * i) (right.words n) :=
      O3.val32 (.inr (by unfold multSlot; omega_using [oh])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3])
    obtain top5 : w32 u5.mem B (out.offset n + 4 * i + 4 * right.words n) = (u4.gpr .ebx).toNat := by
      rw [show out.offset n + 4 * i + 4 * right.words n = out.offset n + 4 * (i + right.words n) by omega_using []]; exact W5
    obtain split := val32_append t.mem B (out.offset n) i (right.words n)
    rw [V1] at split
    rw [show i + 1 + right.words n = i + (right.words n + 1) by omega_using [], val32_append, val32_succ, lo5, w5, top5, V4,
      a3, b3', w3, val32_succ s.mem B (a.offset n) i]
    generalize val32 t.mem B (out.offset n) i = X at *
    generalize val32 t.mem B (out.offset n + 4 * i) (right.words n) = Y at *
    generalize val32 s.mem B (a.offset n) i = A at *
    generalize w32 s.mem B (a.offset n + 4 * i) = a at *
    generalize 2 ^ (32 * i) = P at *
    grind
  · -- The words above it.
    obtain e : left.words n + 2 - i = 1 + (left.words n + 2 - (i + 1)) := by omega_using [hi]
    rw [e, val32_append] at V2
    obtain z : val32 t.mem B (out.offset n + 4 * (i + right.words n) + 4 * 1) (left.words n + 2 - (i + 1)) = 0 := by
      have : 0 < 2 ^ (32 * 1) := Nat.two_pow_pos _
      rcases Nat.eq_zero_of_add_eq_zero V2 with ⟨_, z⟩
      exact (Nat.mul_eq_zero.mp z).resolve_left (by omega_using [])
    rw [show out.offset n + 4 * (i + 1 + right.words n) = out.offset n + 4 * (i + right.words n) + 4 * 1 by omega_using [],
      O5.val32 (.inr (by omega_using [])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3, e]), O4.val32 (.inr (by omega_using [])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3, e]),
      O3.val32 (.inr (by unfold multSlot; omega_using [oh])) (by omega_using [nowrap, lp, rp, ob, ab, bb, ao, bo, ah, bh, oh, head, hi, e3, e])]
    exact z

end

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Prime products use the shared paired native multiplication loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep S arr arr_disj)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def productScalars : List Nat := [128, 132, 136, 140, 144, 148, 152]

theorem primeProduct_ok {s : State} {B : Addr} {Z n out a b k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (ho : out < 32) (ha : a < 32) (hb : b < 32) (oa : out ≠ a) (ob : out ≠ b)
    (boundA : num s.mem B n a < 2 ^ (32 * k)) (boundB : num s.mem B n b < 2 ^ (32 * k)) :
    WP isa (primeProduct out a b) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [out] productScalars s.mem t.mem ∧
      num t.mem B n out = num s.mem B n a * num s.mem B n b ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have sa := arr_disj (w := n) oa
  have sb := arr_disj (w := n) ob
  have head := h.hdr_le
  have L : ProductGeometry Z k k (arr n out) (arr n a) (arr n b) := by
    refine ⟨⟨positive, positive, even, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp only [S, VG.Proof.Rsa.X86.Keys.arr, VG.Impl.Rsa.X86.Keys.hdr] at *
    all_goals omega_arith
  have nk : n / 2 = k := by omega_using [width]
  have L' : ProductGeometry Z (Width.prime.words n) (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr out).offset n) ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr a).offset n) ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr b).offset n) := by
    simpa only [Width.words, VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, nk] using L
  have A := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [width] : k ≤ n) boundA
  have Bv := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [width] : k ≤ n) boundB
  have bound : val32 s.mem B (arr n a) k * val32 s.mem B (arr n b) k < 2 ^ (32 * n) := by
    have lt := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left (val32 s.mem B (arr n a) k) (Nat.le_of_lt (val32_lt s.mem B (arr n b) k)))
      (Nat.mul_lt_mul_of_pos_right (val32_lt s.mem B (arr n a) k) (Nat.two_pow_pos (32 * k)))
    rw [show 32 * n = 32 * k + 32 * k by omega_using [width], Nat.pow_add]
    exact lt
  refine WP.mono (product_ok h L') fun t ⟨ht, O, V, K⟩ => ?_
  simp only [Width.words, VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, nk] at O V
  have value : val32 t.mem B (arr n out) (n + 2) =
      val32 s.mem B (arr n a) k * val32 s.mem B (arr n b) k := by
    simpa only [width, Nat.two_mul, Nat.add_assoc] using V
  refine ⟨ht, ?_, ?_, K⟩
  · intro x hx
    apply O x
    intro r hr
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h0 := hx (128, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h1 := hx (132, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h2 := hx (136, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h3 := hx (140, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h4 := hx (144, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h5 := hx (148, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h6 := hx (152, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      simp only at *
      omega_using [h0, h1, h2, h3, h4, h5, h6]
    · have H := hx (arr n out, S n) (by simp [VG.Proof.Rsa.X86.Keys.ranges])
      simpa only [S, width, Nat.two_mul, Nat.add_assoc] using H
  · have low := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [] : n ≤ n + 2)
      (by rw [value]; exact bound)
    change val32 t.mem B (arr n out) n = _
    rw [low, value, A, Bv]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.Decrement`, which only this module used -/

section

/-! # Saturating predecessors of arbitrary RSA input factors -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aOne kFlag aPa aQa aPm aQm aPhi aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem decTo_ok {s : State} {B : Addr} {Z n out a : Nat}
    (h : Ws s B Z n 32) (ho : out < 32) (ha : a < 32)
    (_oPersistent : 16 ≤ out) (aPersistent : 16 ≤ a) (_oa : out ≠ a)
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa (decTo out a) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, out] [sT, kFlag] s.mem t.mem ∧
      num t.mem B n out = num s.mem B n a - 1 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hFlag : kFlag + 4 ≤ hdr := by decide
  obtain hT : sT + 4 ≤ hdr := by decide
  obtain fa := h.fit64 ha
  unfold decTo seqs
  refine WP.seq (WP.mono (eq_ok h (by decide) ha (by decide)
    (by unfold aT1; omega_using [aPersistent]) (by decide) hFlag) fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  obtain A : num u.mem B n a = num s.mem B n a :=
    Ou.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT1; omega_using [aPersistent])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> with_reducible assumption)
      fa
  obtain Zero : num u.mem B n aZero = 0 := by
    rw [Ou.num (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> with_reducible assumption)
      (h.fit64 (by decide)), zero]
  obtain One : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro d hd; rcases hd with rfl | rfl <;> with_reducible assumption)
      (h.fit64 (by decide)), one]
  rw [zero] at flag
  obtain bit : slot u.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega_using []
  refine WP.seq (WP.mono (sel_ok hu (by decide) (by decide) (by decide) hFlag bit (by decide))
    fun v ⟨hv, Ov, selected, Kv⟩ => ?_)
  obtain Av : num v.mem B n a = num s.mem B n a := by
    rw [Ov.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT2; omega_using [aPersistent]) (by simp) fa, A]
  obtain amount : num v.mem B n aT2 = if num s.mem B n a = 0 then 0 else 1 := by
    rw [selected, flag, One, Zero]
    by_cases p : num s.mem B n a = 0 <;> simp only [p, ite_true, ite_false, Nat.one_ne_zero]
  refine WP.mono (sub_ok hv ho ha (by decide))
    fun t ⟨ht, Ot, value, borrow, Kt⟩ => ?_
  rw [Av, amount] at value
  obtain fits : (if num s.mem B n a = 0 then 0 else 1) ≤ num s.mem B n a := by
    split <;> omega_arith
  obtain noBorrow := (VG.Proof.Rsa.borrow_iff value (val32_lt t.mem B (arr n out) n) borrow).mpr fits
  rw [noBorrow, Nat.mul_zero, Nat.add_zero] at value
  refine ⟨ht, (Ou.join Ov (js := [aT1, aT2, out]) (ds := [sT, kFlag])).join Ot
    (js := [aT1, aT2, out]) (ds := [sT, kFlag]), ?_, ?_⟩
  · by_cases p : num s.mem B n a = 0
    · simp only [p, ite_true] at value ⊢
      omega_using [value]
    · simp only [p, ite_false] at value
      omega_using [value]
  · exact Ku.trans ((Kv.mono (by decide)).trans Kt)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Sorted factors, saturated predecessors, and their exact full product -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Order.lean`, which only this module imported.
section

/-! # The native factor sort preserves both values and hides their ordering -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag aPa aQa aPm aQm aPhi aHalf)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem order_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (order) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, aPa, aQa] [kFlag] s.mem t.mem ∧
      num t.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hf : kFlag + 4 ≤ hdr := by decide
  obtain fp := h.fit64 (j := aPa) (by decide)
  obtain fq := h.fit64 (j := aQa) (by decide)
  obtain ft := h.fit64 (j := aT2) (by decide)
  unfold order seqs
  refine WP.seq (WP.mono (sub_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, subtract, bit, Ku⟩ => ?_)
  obtain borrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) bit
  obtain pu : num u.mem B n aPa = num s.mem B n aPa := Ou.num (by decide) (by simp) fp
  obtain qu : num u.mem B n aQa = num s.mem B n aQa := Ou.num (by decide) (by simp) fq
  refine WP.seq (WP.mono (store_slot hu hf .ebx) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  obtain pv : num v.mem B n aPa = num s.mem B n aPa := by
    rw [Ov.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fp, pu]
  obtain qv : num v.mem B n aQa = num s.mem B n aQa := by
    rw [Ov.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fq, qu]
  refine WP.seq (WP.mono (copy_ok hv (by decide) (by decide) (by decide)) fun w ⟨hw, Ow, copied, Kw, _⟩ => ?_)
  obtain pw : num w.mem B n aPa = num s.mem B n aPa := by rw [Ow.num (by decide) (by simp) fp, pv]
  obtain qw : num w.mem B n aQa = num s.mem B n aQa := by rw [Ow.num (by decide) (by simp) fq, qv]
  obtain tw : num w.mem B n aT2 = num s.mem B n aPa := copied.trans pv
  obtain fw : slot w.mem B kFlag = (u.gpr .ebx).toNat := by rw [Ow.slot hf (by simp), flag]
  obtain bw : slot w.mem B kFlag ≤ 1 := by rw [fw]; exact bit
  refine WP.seq (WP.mono (sel_ok hw (by decide) (by decide) (by decide) hf bw (by decide))
    fun x ⟨hx, Ox, selectedP, Kx⟩ => ?_)
  obtain qx : num x.mem B n aQa = num s.mem B n aQa := by rw [Ox.num (by decide) (by simp) fq, qw]
  obtain tx : num x.mem B n aT2 = num s.mem B n aPa := by rw [Ox.num (by decide) (by simp) ft, tw]
  obtain fx : slot x.mem B kFlag = (u.gpr .ebx).toNat := by rw [Ox.slot hf (by simp), fw]
  obtain bx : slot x.mem B kFlag ≤ 1 := by rw [fx]; exact bit
  refine WP.mono (sel_ok hx (by decide) (by decide) (by decide) hf bx (by decide))
    fun t ⟨ht, Ot, selectedQ, Kt⟩ => ?_
  obtain finalP : num t.mem B n aPa =
      if (u.gpr .ebx).toNat = 0 then num s.mem B n aPa else num s.mem B n aQa := by
    rw [Ot.num (by decide) (by simp) fp, selectedP, fw, pw, qw]
  obtain finalQ : num t.mem B n aQa =
      if (u.gpr .ebx).toNat = 0 then num s.mem B n aQa else num s.mem B n aPa := by
    rw [selectedQ, fx, qx, tx]
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag])).join Ow
    (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag])).join Ox
    (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag])).join Ot
    (js := [aT1, aT2, aPa, aQa]) (ds := [kFlag]), ?_, ?_,
    Ku.trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans
      ((Kx.mono (by decide)).trans (Kt.mono (by decide)))))⟩
  · rw [finalP]
    by_cases p : (u.gpr .ebx).toNat = 0
    · rw [ite_eq_left p, Nat.max_eq_left (borrow.mp p)]
    · have lt : num s.mem B n aPa < num s.mem B n aQa := by
        obtain neg : ¬num s.mem B n aQa ≤ num s.mem B n aPa := fun le => p (borrow.mpr le)
        omega
      simp only [p, ite_false, Nat.max_eq_right (Nat.le_of_lt lt)]
  · rw [finalQ]
    by_cases p : (u.gpr .ebx).toNat = 0
    · rw [ite_eq_left p, Nat.min_eq_right (borrow.mp p)]
    · have lt : num s.mem B n aPa < num s.mem B n aQa := by
        obtain neg : ¬num s.mem B n aQa ≤ num s.mem B n aPa := fun le => p (borrow.mpr le)
        omega
      simp only [p, ite_false, Nat.min_eq_left (Nat.le_of_lt lt)]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aPm aQm aPhi aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def primesArrays : List Nat := [aT1, aT2, aPa, aQa, aPm, aQm, aPhi]
def primesScalars : List Nat := [kFlag, sT] ++ productScalars

theorem primes_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa primes s fun t =>
      Ws t B Z n 32 ∧ Keep B n primesArrays primesScalars s.mem t.mem ∧
      num t.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) ∧
      num t.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 ∧
      num t.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 ∧
      num t.mem B n aPhi = num t.mem B n aPm * num t.mem B n aQm ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let P := max (num s.mem B n aPa) (num s.mem B n aQa)
  let Q := min (num s.mem B n aPa) (num s.mem B n aQa)
  obtain pBound : P < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  obtain qBound : Q < 2 ^ (32 * k) := Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  unfold primes seqs
  refine WP.seq (WP.mono (order_ok h) fun u ⟨hu, Ou, Pu, Qu, Ku⟩ => ?_)
  obtain Zu : num u.mem B n aZero = 0 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans zero
  obtain oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  refine WP.seq (WP.mono (decTo_ok hu (by decide) (by decide) (by decide) (by decide) (by decide) Zu oneU)
    fun v ⟨hv, Ov, Pm, Kv⟩ => ?_)
  rw [Pu] at Pm
  obtain Pv : num v.mem B n aPa = P :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans Pu
  obtain Qv : num v.mem B n aQa = Q :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans Qu
  obtain Zv : num v.mem B n aZero = 0 :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans Zu
  obtain oneV : num v.mem B n aOne = 1 :=
    (Ov.num (by decide) (by decide) (h.fit64 (by decide))).trans oneU
  refine WP.seq (WP.mono (decTo_ok hv (by decide) (by decide) (by decide) (by decide) (by decide) Zv oneV)
    fun w ⟨hw, Ow, Qm, Kw⟩ => ?_)
  rw [Qv] at Qm
  obtain Pw : num w.mem B n aPa = P :=
    (Ow.num (by decide) (by decide) (h.fit64 (by decide))).trans Pv
  obtain Qw : num w.mem B n aQa = Q :=
    (Ow.num (by decide) (by decide) (h.fit64 (by decide))).trans Qv
  obtain Pmw : num w.mem B n aPm = P - 1 :=
    (Ow.num (by decide) (by decide) (h.fit64 (by decide))).trans Pm
  refine WP.mono (primeProduct_ok hw width positive even (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [Pmw]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound))
    fun t ⟨ht, Ot, product, Kt⟩ => ?_
  obtain Pt : num t.mem B n aPa = P :=
    (Ot.num (by decide) (by decide) (h.fit64 (by decide))).trans Pw
  obtain Qt : num t.mem B n aQa = Q :=
    (Ot.num (by decide) (by decide) (h.fit64 (by decide))).trans Qw
  obtain Pmt : num t.mem B n aPm = num w.mem B n aPm := Ot.num (by decide) (by decide) (h.fit64 (by decide))
  obtain Qmt : num t.mem B n aQm = num w.mem B n aQm := Ot.num (by decide) (by decide) (h.fit64 (by decide))
  refine ⟨ht, ?_, Pt, Qt, Pmt.trans Pmw, Qmt.trans Qm, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · have first : Keep B n primesArrays primesScalars s.mem u.mem := Ou.mono (by decide) (by decide)
    obtain second : Keep B n primesArrays primesScalars u.mem v.mem := Ov.mono (by decide) (by decide)
    obtain third : Keep B n primesArrays primesScalars v.mem w.mem := Ow.mono (by decide) (by decide)
    obtain last : Keep B n primesArrays primesScalars w.mem t.mem := Ot.mono (by decide) (by decide)
    exact ((first.trans second).trans third).trans last
  · rw [Pmt, Qmt]
    exact product

end VG.Proof.RsaKeyGen.X86.KeyRuntime
