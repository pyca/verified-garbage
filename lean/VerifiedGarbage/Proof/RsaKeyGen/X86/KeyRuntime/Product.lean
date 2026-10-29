module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductLayout

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Product
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table2
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
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
  rw [PtrAt, h.old.workspace.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

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
    cases w <;> simp only [Width.words] <;> omega
  have lb := wBound left
  have rb := wBound right
  unfold productZero
  simp only [List.append_assoc]
  refine WP.seq (h.ptr_ok out (by decide) (by decide) (by omega) fun u K1 m1 P1 => ?_)
  have hu := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine hu.bytes_ok left .ecx fun v K2 m2 cl => ?_
  have hv := hu.keep K2 (by rw [m2]; exact Outside.refl _ _ _ _)
  refine hv.bytes_ok right .eax fun w K3 m3 cr => ?_
  refine wp_addS rfl fun a A _ => wp_addS rfl fun b Bb _ => wp_movS rfl fun c U _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebp] s c :=
    (((K1.mono (by decide)).trans (K2.mono (by decide))).trans (K3.mono (by decide))).trans
      (((A.keeps.mono (by decide)).trans (Bb.keeps.mono (by decide))).trans (U.keeps.mono (by decide)))
  have m : c.mem = s.mem := by rw [U.mem, Bb.mem, A.mem, m3, m2, m1]
  have pointer : PtrAt c B .ebp (out.offset n) := by
    rw [PtrAt, U.other _ (by decide), Bb.other _ (by decide), A.other _ (by decide), K3.1 _ (by decide),
      K2.1 _ (by decide)]
    exact P1
  have ecx : (c.gpr .ecx).toNat = 4 * (left.words n + right.words n + 2) := by
    rw [U.other _ (by decide), Bb.gpr, A.gpr, BitVec.toNat_add, BitVec.toNat_add, cr, K3.1 _ (by decide), cl]
    change ((4 * left.words n + 4 * right.words n) % 2 ^ 32 + 8) % 2 ^ 32 = _
    omega
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok (h.full.rt.of_keeps K)
    (by omega : 0 < left.words n + right.words n + 2) fit pointer ecx U.gpr) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O
  have allK := K.trans (Kt.mono (by decide))
  exact ⟨h.keep allK (O.mono (Nat.zero_le _) (by omega)), O, V, allK⟩

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
  refine h.ptr_ok out (r := .eax) (t := .edx) (by decide) (by decide) (by omega) fun u1 K1 m1 P1 => ?_
  have h1 := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine wp_movS rfl fun u2 U2 _ => wp_subS rfl fun u3 U3 _ => ?_
  have K3 : Keeps [.eax, .edx, .ecx] s u3 := ((K1.mono (by decide)).trans (U2.keeps.mono (by decide))).trans
    (U3.keeps.mono (by decide))
  have m3 : u3.mem = s.mem := by rw [U3.mem, U2.mem, m1]
  have ebp3 : PtrAt u3 B .ebp (out.offset n + 4 * i) := by rw [PtrAt, K3.1 _ (by decide)]; exact P
  have ecx3 : (u3.gpr .ecx).toNat = 4 * i := by
    have e2 : u2.gpr .ecx = u1.gpr .ebp := U2.gpr
    have pe : PtrAt u1 B .ebp (out.offset n + 4 * i) := by rw [PtrAt, K1.1 _ (by decide)]; exact P
    have pa : (u2.gpr .eax).toNat = (B.toNat + out.offset n) % 2 ^ 32 := by rw [U2.other _ (by decide)]; exact P1
    rw [U3.gpr, BitVec.toNat_sub, e2, pa, pe]
    omega
  have h3 := h.keep K3 (by rw [m3]; exact Outside.refl _ _ _ _)
  refine h3.ptr_ok a (r := .eax) (t := .edx) (by decide) (by decide) (by omega) fun u4 K4 m4 P4 => ?_
  refine wp_addS rfl fun u5 U5 _ => ?_
  have K5 : Keeps [.eax, .edx, .ecx] s u5 := (K3.trans (K4.mono (by decide))).trans (U5.keeps.mono (by decide))
  have m5 : u5.mem = s.mem := by rw [U5.mem, m4, m3]
  have h5 := h.keep K5 (by rw [m5]; exact Outside.refl _ _ _ _)
  have eax5 : PtrAt u5 B .eax (a.offset n + 4 * i) := by
    rw [PtrAt, U5.gpr, ptr_add P4, K4.1 _ (by decide), ecx3]
  refine wp_movS (readSrc_ptr h5.full.rt eax5 (d := 0) (by omega)) fun u6 U6 _ => ?_
  have K6 : Keeps [.eax, .edx, .ecx] s u6 := K5.trans (U6.keeps.mono (by decide))
  have h6 := h.keep K6 (by rw [U6.mem, m5]; exact Outside.refl _ _ _ _)
  refine wp_storeS (ea_ptr h6.full.rt h6.edi_at (d := multSlot) (by unfold multSlot; omega))
    (ws_write h6.full.rt (y := 0 + multSlot) (n := 4) (by unfold multSlot; omega)) fun u7 U7 => ?_
  have m7 : u7.mem = s.mem.writeW (off B multSlot) (u6.gpr .edx) := by
    rw [U7.mem, U6.mem, m5, Nat.zero_add]
  have O7 : Outside B multSlot 4 s.mem u7.mem := by
    rw [m7]; exact writeW32_outside _ _ _ (by unfold multSlot; omega)
  have K7 : Keeps [.eax, .edx, .ecx] s u7 := K6.widen (U7.keeps [])
  have h7 := h.keep K7 (O7.mono (Nat.zero_le _) (by unfold multSlot; omega))
  refine h7.ptr_ok b (r := .ecx) (t := .edx) (by decide) (by decide) (by omega) fun u8 K8 m8 P8 => ?_
  have h8 := h7.keep K8 (by rw [m8]; exact Outside.refl _ _ _ _)
  refine h8.bytes_ok right .esi fun u9 K9 m9 e9 => ?_
  refine wp_movS rfl fun u U _ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u :=
    (((K7.mono (by decide)).trans (K8.mono (by decide))).trans (K9.mono (by decide))).trans (U.keeps.mono (by decide))
  have m : u.mem = u7.mem := by rw [U.mem, m9, m8]
  refine ⟨h.keep K (by rw [m]; exact O7.mono (Nat.zero_le _) (by unfold multSlot; omega)), by rw [m]; exact O7,
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
    cases w <;> simp only [Width.words] <;> omega
  have rb := wBound right
  have lb := wBound left
  unfold productNext
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_storeS (ea_ptr h.full.rt P (d := 0) (by omega))
    (ws_write h.full.rt (y := out.offset n + 4 * i + 4 * right.words n + 0) (n := 4) (by omega)) fun u1 U1 => ?_
  have O1 : Outside B (out.offset n + 4 * (i + right.words n)) 4 s.mem u1.mem := by
    rw [U1.mem, show out.offset n + 4 * (i + right.words n) = out.offset n + 4 * i + 4 * right.words n + 0 by omega]
    exact writeW32_outside _ _ _ (by omega)
  have h1 := h.keep (U1.keeps []) (O1.mono (Nat.zero_le _) (by omega))
  refine h1.bytes_ok right .eax fun u2 K2 m2 e2 => ?_
  refine wp_subS rfl fun u3 U3 _ => wp_addS rfl fun u4 U4 _ => ?_
  have K4 : Keeps [.eax, .ebp] s u4 :=
    (((U1.keeps []).mono (by decide)).trans (K2.mono (by decide))).trans ((U3.keeps.trans U4.keeps).mono (by decide))
  have m4 : u4.mem = u1.mem := by rw [U4.mem, U3.mem, m2]
  have h4 := h.keep K4 (by rw [m4]; exact O1.mono (Nat.zero_le _) (by omega))
  have ebp2 : PtrAt u2 B .ebp (out.offset n + 4 * i + 4 * right.words n) := by
    rw [PtrAt, K2.1 _ (by decide), U1.gpr]; exact P
  have ebp3 : PtrAt u3 B .ebp (out.offset n + 4 * i) := by
    rw [PtrAt, U3.gpr, ptr_sub ebp2 _ (by rw [e2]; omega), e2]; congr 2; omega
  have ebp4 : PtrAt u4 B .ebp (out.offset n + 4 * (i + 1)) := by
    rw [PtrAt, U4.gpr, ptr_add ebp3, show (4 : BitVec 32).toNat = 4 from rfl]; congr 2
  refine h4.ptr_ok out (r := .eax) (t := .edx) (by decide) (by decide) (by omega) fun u5 K5 m5 P5 => ?_
  have h5 := h4.keep K5 (by rw [m5]; exact Outside.refl _ _ _ _)
  refine h5.bytes_ok left .edx fun u6 K6 m6 e6 => ?_
  refine wp_addS rfl fun u7 U7 _ => wp_cmpS rfl fun u F z => WP.block_nil ?_
  have K : Keeps [.eax, .edx, .ebp] s u :=
    (((K4.mono (by decide)).trans (K5.mono (by decide))).trans (K6.mono (by decide))).trans
      ((U7.keeps.mono (by decide)).trans (F.keeps _))
  have m : u.mem = u1.mem := by rw [F.mem, U7.mem, m6, m5, m4]
  have ebp7 : PtrAt u7 B .ebp (out.offset n + 4 * (i + 1)) := by
    rw [PtrAt, U7.other _ (by decide), K6.1 _ (by decide), K5.1 _ (by decide)]; exact ebp4
  have eax7 : PtrAt u7 B .eax (out.offset n + 4 * left.words n) := by
    rw [PtrAt, U7.gpr, ptr_add (x := out.offset n) (by rw [PtrAt, K6.1 _ (by decide)]; exact P5), e6]
  refine ⟨h.keep K (by rw [m]; exact O1.mono (Nat.zero_le _) (by omega)), by rw [m]; exact O1, ?_,
    by rw [PtrAt, F.gpr]; exact ebp7, ?_, K⟩
  · rw [m, U1.mem, show out.offset n + 4 * (i + right.words n) = out.offset n + 4 * i + 4 * right.words n + 0 by omega,
      w32_write_self]
  · rw [z, VG.Proof.Bignum.X86.CrtRt.ptr_beq ebp7 eax7 (by omega) (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)

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
  have ranges : ∀ r ∈ productRanges (left.words n) (right.words n) (out.offset n), r.1 + r.2 ≤ Z := by
    intro r mem
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> dsimp only <;> omega
  have keepA {m : Mem} (O : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem m) (k : Nat)
      (hk : k ≤ left.words n) : val32 m B (a.offset n) k = val32 s.mem B (a.offset n) k :=
    O.val32 (fun r mem => by
      simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> dsimp only <;> omega) (by omega)
  have keepB {m : Mem} (O : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem m) :
      val32 m B (b.offset n) (right.words n) = val32 s.mem B (b.offset n) (right.words n) :=
    O.val32 (fun r mem => by
      simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> dsimp only <;> omega) (by omega)
  let Bv := val32 s.mem B (b.offset n) (right.words n)
  unfold product
  refine WP.seq (WP.mono (productZero_ok h left right out ob) fun u1 ⟨h1, O1, Z1, K1⟩ => ?_)
  rw [← List.append_nil (ptr out .ebp .edx)]
  refine WP.seq (h1.ptr_ok out (r := .ebp) (t := .edx) (by decide) (by decide) (by omega)
    fun u2 K2 m2 P2 => WP.block_nil ?_)
  have h2 := h1.keep K2 (by rw [m2]; exact Outside.refl _ _ _ _)
  have O2 : Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem u2.mem := by
    rw [m2]; exact Outs.of_outside O1 (by simp [productRanges])
  have Z2 := Z1
  rw [← m2, show left.words n + right.words n + 2 = right.words n + (left.words n + 2) by omega, val32_append] at Z2
  have Zlo : val32 u2.mem B (out.offset n) (right.words n) = 0 := by omega
  have Zhi : val32 u2.mem B (out.offset n + 4 * right.words n) (left.words n + 2) = 0 := by
    have : 0 < 2 ^ (32 * right.words n) := Nat.two_pow_pos _
    rcases Nat.eq_zero_of_add_eq_zero Z2 with ⟨_, z⟩
    exact (Nat.mul_eq_zero.mp z).resolve_left (by omega)
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop (N := left.words n) lp (fun i t =>
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧ Ws t B Z n N ∧ PtrAt t B .ebp (out.offset n + 4 * i) ∧
      Outs B (productRanges (left.words n) (right.words n) (out.offset n)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (i + right.words n) = val32 s.mem B (a.offset n) i * Bv ∧
      val32 t.mem B (out.offset n + 4 * (i + right.words n)) (left.words n + 2 - i) = 0) ?step
    ⟨(K1.mono (by decide)).trans (K2.mono (by decide)), h2, by simpa using P2, O2,
      by simpa [val32] using Zlo, by simpa using Zhi⟩)
    fun t ⟨K, ht, _, O, V1, V2⟩ => ⟨ht, O, ?fin, K⟩
  case fin =>
    rw [show left.words n + 2 - left.words n = 2 by omega] at V2
    rw [show left.words n + right.words n + 2 = (left.words n + right.words n) + 2 by omega, val32_append, V1, V2,
      Nat.mul_zero, Nat.add_zero]
  rintro i t hi ⟨Kt, It, pt, Ot, V1, V2⟩
  -- The multiplier and the pointers.
  refine WP.seq (WP.mono (productRow_ok It right out a b (i := i) (by omega) bb rp (by omega) pt)
    fun u3 ⟨I3, O3, M3, c3, e3, b3, p3, K3⟩ => ?_)
  have edi3 := I3.edi_at
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.CrtRt.rowLoopAt_ok (mo := multSlot) I3.full.rt (S := 0)
    (bx := b.offset n) (w := out.offset n + 4 * i) (N := right.words n) rp edi3 c3 p3 e3 b3
    (by unfold multSlot; omega) bb (by omega) (by omega) (.inl (by unfold multSlot; omega)))
    fun u4 ⟨O4, V4, p4, K4⟩ => ?_)
  have I4 := I3.keep K4 (O4.mono (Nat.zero_le _) (by omega))
  refine WP.mono (productNext_ok I4 left right out hi ob p4) fun u5 ⟨I5, O5, W5, p5, z5, K5⟩ =>
    ⟨⟨?_, I5, p5, ?_, ?_, ?_⟩, z5⟩
  · exact ((Kt.trans (K3.mono (by decide))).trans (K4.mono (by decide))).trans (K5.mono (by decide))
  · refine Ot.trans ((Outs.of_outside (O3.mono (o' := 128) (n' := 28) (by unfold multSlot; omega)
      (by unfold multSlot; omega)) (by simp [productRanges])).trans ((Outs.of_outside
      (O4.mono (o' := out.offset n) (n' := 4 * (left.words n + right.words n + 2)) (by omega) (by omega))
      (by simp [productRanges])).trans (Outs.of_outside
      (O5.mono (o' := out.offset n) (n' := 4 * (left.words n + right.words n + 2)) (by omega) (by omega))
      (by simp [productRanges]))))
  · -- The new row's value.
    have a3 : w32 u3.mem B (0 + multSlot) = w32 s.mem B (a.offset n + 4 * i) := by
      rw [Nat.zero_add, M3]
      have e := keepA Ot (i + 1) (by omega)
      rw [val32_succ, val32_succ, keepA Ot i (by omega)] at e
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel e)
    have b3' : val32 u3.mem B (b.offset n) (right.words n) = Bv := by
      rw [O3.val32 (.inr (by unfold multSlot; omega)) (by omega)]; exact keepB Ot
    have lo5 : val32 u5.mem B (out.offset n) i = val32 t.mem B (out.offset n) i := by
      rw [O5.val32 (.inl (by omega)) (by omega), O4.val32 (.inl (by omega)) (by omega),
        O3.val32 (.inr (by unfold multSlot; omega)) (by omega)]
    have w5 : val32 u5.mem B (out.offset n + 4 * i) (right.words n) =
        val32 u4.mem B (out.offset n + 4 * i) (right.words n) :=
      O5.val32 (.inl (by omega)) (by omega)
    have w3 : val32 u3.mem B (out.offset n + 4 * i) (right.words n) =
        val32 t.mem B (out.offset n + 4 * i) (right.words n) :=
      O3.val32 (.inr (by unfold multSlot; omega)) (by omega)
    have top5 : w32 u5.mem B (out.offset n + 4 * i + 4 * right.words n) = (u4.gpr .ebx).toNat := by
      rw [show out.offset n + 4 * i + 4 * right.words n = out.offset n + 4 * (i + right.words n) by omega]; exact W5
    have split := val32_append t.mem B (out.offset n) i (right.words n)
    rw [V1] at split
    rw [show i + 1 + right.words n = i + (right.words n + 1) by omega, val32_append, val32_succ, lo5, w5, top5, V4,
      a3, b3', w3, val32_succ s.mem B (a.offset n) i]
    generalize val32 t.mem B (out.offset n) i = X at *
    generalize val32 t.mem B (out.offset n + 4 * i) (right.words n) = Y at *
    generalize val32 s.mem B (a.offset n) i = A at *
    generalize w32 s.mem B (a.offset n + 4 * i) = a at *
    generalize 2 ^ (32 * i) = P at *
    grind
  · -- The words above it.
    have e : left.words n + 2 - i = 1 + (left.words n + 2 - (i + 1)) := by omega
    rw [e, val32_append] at V2
    have z : val32 t.mem B (out.offset n + 4 * (i + right.words n) + 4 * 1) (left.words n + 2 - (i + 1)) = 0 := by
      have : 0 < 2 ^ (32 * 1) := Nat.two_pow_pos _
      rcases Nat.eq_zero_of_add_eq_zero V2 with ⟨_, z⟩
      exact (Nat.mul_eq_zero.mp z).resolve_left (by omega)
    rw [show out.offset n + 4 * (i + 1 + right.words n) = out.offset n + 4 * (i + right.words n) + 4 * 1 by omega,
      O5.val32 (.inr (by omega)) (by omega), O4.val32 (.inr (by omega)) (by omega),
      O3.val32 (.inr (by unfold multSlot; omega)) (by omega)]
    exact z

end

end VG.Proof.RsaKeyGen.X86.KeyRuntime
