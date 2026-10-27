module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Double
public import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn

/-! # The power of two of the precomputation at a run-time width

`-M⁻¹ mod 2³²` at 152 (`inverse_ok`); number 4 set to `2^(8 (n_len - 1))`
(`seed_ok`), `esi` to the number of doublings that take it to `2^(65 W)`
(`count_ok`), and the doublings (`doublings_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputeFn

/-! ## The inverse -/

theorem inverse_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) (hodd : val32 s.mem base numOff (nw len) % 2 = 1) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)) s fun t =>
      (val32 s.mem base numOff (nw len) * w32 t.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Outside base invOff 4 s.mem t.mem ∧ Keeps clob s t := by
  have f0 := (h.fits (j := 0) (by decide)).1
  have dims := h.dimensions
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  rw [n0] at f0
  have b264 : 264 ≤ bytes := by have := dims.1; simp only [wb] at f0; omega
  obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega⟩
  have hodd' : w32 s.mem base numOff % 2 = 1 := by
    rw [hk, VG.Proof.Mont.X86.Dynamic.val32_parity] at hodd; exact hodd
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok h.scratch (mo := numOff) (inv := invOff)
    (by simp only [numOff]; omega) (by simp only [invOff]; omega) hodd') fun t ⟨I, O, K⟩ => ⟨?_, O, K⟩
  rw [hk, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
  exact I

/-! ## The seed -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `add eax, eax`, `j` times: `eax` times `2^j`. -/
theorem dbls_ok (j : Nat)
    (k : ∀ u, Keeps [.eax] s u → u.mem = s.mem → (u.gpr .eax).toNat = (s.gpr .eax).toNat * 2 ^ j % 2 ^ 32 →
      WP isa (.block is) u Q) :
    WP isa (.block (List.replicate j (.alu .add .eax (.reg .eax)) ++ is)) s Q := by
  induction j generalizing s with
  | zero => exact k s (Keeps.refl _ _) rfl (by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (s.gpr .eax).isLt])
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append]
    refine wp_addS rfl fun s₁ u₁ _ => ih fun u K m e => k u (u₁.keeps.trans K) (m.trans u₁.mem) ?_
    rw [e, u₁.gpr, BitVec.toNat_add, Nat.mod_mul_mod, Nat.add_mul, show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ 2 j,
      ← Nat.mul_assoc, Nat.mul_two]
end

/-- A byte written into memory: at its address the byte, elsewhere as it was. -/
theorem write_byte (m : Mem) (A : Addr) {p j : Nat} (v : Byte) (hp : p < 2 ^ 32) (hj : j < 2 ^ 32) :
    (m.writeW (A + BitVec.ofNat 64 p) v) (A + BitVec.ofNat 64 j) =
      if j = p then v else m (A + BitVec.ofNat 64 j) := by
  have e : A + BitVec.ofNat 64 j - (A + BitVec.ofNat 64 p) = BitVec.ofNat 64 j - BitVec.ofNat 64 p := by
    rw [Offset.add_sub_add_left]
  simp only [Mem.writeW, Mem.write, e]
  by_cases hjp : j = p
  · subst hjp
    simp
  · have : ¬ (BitVec.ofNat 64 j - BitVec.ofNat 64 p).toNat < 8 / 8 := by
      rw [BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (a := p) (by omega)]
      omega
    simp only [this, hjp, ite_false]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : Byte) (h : d + 1 ≤ 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [VG.Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- A one in byte `p` of a number that was zero: `2^(8 p)`. -/
theorem val32_one_byte {m : Mem} {base : Addr} {d n p : Nat} (Z : val32 m base d n = 0) (hp : p < 4 * n)
    (hn : 4 * n < 2 ^ 32) :
    val32 (m.writeW (off base d + BitVec.ofNat 64 p) (1 : Byte)) base d n = 2 ^ (8 * p) := by
  rw [← read_eq_val32]
  have hb : ∀ j < 4 * n, (m.writeW (off base d + BitVec.ofNat 64 p) (1 : Byte)) (off base d + BitVec.ofNat 64 j) =
      if j = p then 1 else 0 := by
    intro j hj
    rw [write_byte _ _ _ (by omega) (by omega)]
    split
    · rfl
    · exact byte_zero_of_val32 Z hj
  obtain ⟨k, hk⟩ : ∃ k, 4 * n - p = k + 1 := ⟨4 * n - p - 1, by omega⟩
  rw [show 4 * n = k + 1 + p by omega, read_toNat_add, read_toNat_succ,
    VG.Proof.Bignum.read_zero_bytes _ _ p (fun j hj => by rw [hb j (by omega), ite_eq_right (by omega)]),
    VG.Proof.Bignum.read_zero_bytes _ _ k (fun j hj => by
      rw [show off base d + BitVec.ofNat 64 p + 1 + BitVec.ofNat 64 j = off base d + BitVec.ofNat 64 (p + 1 + j) by
        rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.add_add, Offset.add_add, Nat.add_assoc]]
      rw [hb _ (by omega), ite_eq_right (by omega)]),
    hb p hp, ite_eq_left rfl]
  simp

theorem seed_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa PrecomputeFn.seed s fun u => Outside base (numAt len 4) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len 4) (nw len) = 2 ^ (8 * (len - 1)) ∧ Keeps [.eax, .ecx, .ebp] s u := by
  have fit := (h.fits (j := 4) (by decide)).1
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have wbl := wb_le h.upper
  have lw := len_le_wb len
  have hlow := h.lower
  unfold PrecomputeFn.seed
  refine WP.seq (WP.mono (zero_ok h (j := 4) (by decide)) fun u ⟨O, Z, K⟩ => ?_)
  have hu := h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega))
  refine slotPtr_ok (r := .ebp) (t := .ecx) (by decide) (by decide) hu.edi hu.width h.upper (by decide)
    fun v Kv mv pv _ => wp_movS (hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)).width
      fun v₁ u₁ _ => wp_addS rfl fun v₂ u₂ _ => wp_subS rfl fun v₃ u₃ _ => wp_movS rfl fun v₄ u₄ _ => ?_
  have K₄ : Keeps [.eax, .ecx, .ebp] u v₄ :=
    ((((Kv.mono (by decide)).trans (u₁.keeps.mono (by decide))).trans (u₂.keeps.mono (by decide))).trans
      (u₃.keeps.mono (by decide))).trans (u₄.keeps.mono (by decide))
  have hv₄ := hu.ws.of_keeps K₄
  have pv' : (v.gpr .ebp).toNat = base.toNat + numAt len 4 := by rw [pv, Nat.mod_eq_of_lt (by omega)]
  have p₄ : PtrAt v₄ base .ebp (numAt len 4 + (len - 1)) := by
    rw [PtrAt, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), u₁.gpr,
      BitVec.toNat_sub, BitVec.toNat_add, pv', BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine wp_store8 (ea_ptr hv₄ p₄ (d := 0) (by omega)) (ws_write hv₄ (y := numAt len 4 + (len - 1) + 0) (n := 1)
    (by omega)) fun w m => WP.block_nil ?_
  have mv₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  have one : (v₄.gpr Reg8.al.reg).setWidth 8 = (1 : Byte) := by
    show (v₄.gpr .eax).setWidth 8 = _
    rw [u₄.gpr]; rfl
  refine ⟨?_, ?_, (K.trans K₄).trans (m.keeps _)⟩
  · rw [m.mem, mv₄, one, Nat.add_zero]
    exact O.trans ((writeW8_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [m.mem, mv₄, one, Nat.add_zero, show off base (numAt len 4 + (len - 1)) =
      off base (numAt len 4) + BitVec.ofNat 64 (len - 1) by rw [off, off, Offset.add_add]]
    exact val32_one_byte Z (by omega) (by omega)

/-! ## The doublings -/

theorem count_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa (.block PrecomputeFn.count) s fun u => (u.gpr .esi).toNat = 65 * Spec.Rsa.modulusWords len + 8 - 8 * len ∧
      u.mem = s.mem ∧ Keeps [.eax, .esi] s u := by
  have hl := h.upper
  have hw := h.width
  unfold PrecomputeFn.count
  simp only [List.cons_append, List.append_assoc]
  refine wp_movS hw fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => PublicRt.wp_shr (by decide) fun s₃ u₃ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => dbls_ok 6 fun s₅ K₅ m₅ e₅ => ?_
  simp only [List.nil_append]
  refine wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => ?_
  have K₇ : Keeps [.eax, .esi] s s₇ :=
    (((((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (K₅.mono (by decide))).trans
      ((u₆.keeps.mono (by decide)).trans (u₇.keeps.mono (by decide)))
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_movS (h.keep K₇ (by decide) (by decide) (by rw [m₇]; exact Outside.refl _ _ _ _)).width fun s₈ u₈ _ => dbls_ok 3 fun s₉ K₉ m₉ e₉ => ?_
  refine wp_subS rfl fun t ut _ => WP.block_nil ⟨?_, by rw [ut.mem, m₉, u₈.mem, m₇],
    (K₇.trans ((u₈.keeps.mono (by decide)).trans (K₉.mono (by decide)))).trans (ut.keeps.mono (by decide))⟩
  have W : (s₃.gpr .esi).toNat = Spec.Rsa.modulusWords len := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr]
    have e7 : (7 : BitVec 32).toNat = 7 := rfl
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, e7, Nat.shiftRight_eq_div_pow,
      Spec.Rsa.modulusWords]
    omega
  have e8 : (s₉.gpr .eax).toNat = 8 * len := by
    rw [e₉, u₈.gpr, BitVec.toNat_ofNat]
    omega
  have esi₉ : (s₉.gpr .esi).toNat = 65 * Spec.Rsa.modulusWords len + 8 := by
    rw [K₉.1 _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, K₅.1 _ (by decide), u₄.other _ (by decide)]
    have e8' : (8 : BitVec 32).toNat = 8 := rfl
    simp only [BitVec.toNat_add, e₅, u₄.gpr, W, e8']
    have := h.dimensions
    omega
  rw [ut.gpr, BitVec.toNat_sub, esi₉, e8]
  have := h.dimensions
  unfold Spec.Rsa.modulusWords at *
  omega

theorem doublings_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) {N : Nat} (hN : 0 < N) (hesi : (s.gpr .esi).toNat = N)
    (hT : val32 s.mem base (numAt len 4) (nw len) < val32 s.mem base (numAt len 0) (nw len)) :
    WP isa (.loop (doubleStep 4) .ne) s fun u =>
      Outside base (numAt len 4) (2 * wb len + 4) s.mem u.mem ∧
      val32 u.mem base (numAt len 4) (nw len) =
        val32 s.mem base (numAt len 4) (nw len) * 2 ^ N % val32 s.mem base (numAt len 0) (nw len) ∧
      u.gpr .edi = s.gpr .edi ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have wbe := wb_eq len
  have e04 : numAt len 4 = numAt len 0 + 4 * wb len := by simp only [numAt]; omega
  have e45 : numAt len 5 = numAt len 4 + wb len := numAt_succ len 4
  have nw' := h.scratch.nowrap
  let M := val32 s.mem base (numAt len 0) (nw len)
  let T := val32 s.mem base (numAt len 4) (nw len)
  have hM : 0 < M := by omega
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧ t.gpr .edi = s.gpr .edi ∧
      Outside base (numAt len 4) (2 * wb len + 4) s.mem t.mem ∧
      val32 t.mem base (numAt len 4) (nw len) = T * 2 ^ j % M ∧ (t.gpr .esi).toNat = N - j
  have I₀ : I 0 s := ⟨Keeps.refl _ _, rfl, Outside.refl _ _ _ _,
    by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT], by rw [hesi]; rfl⟩
  refine WP.mono (countLoop (N := N) hN I ?_ I₀) fun t ⟨Kt, edit, Ot, Vt, _⟩ => ⟨Ot, Vt, edit, Kt⟩
  rintro j t hj ⟨Kt, edit, Ot, Vt, esit⟩
  have Ot' : Outside base 0 bytes s.mem t.mem := Ot.mono (Nat.zero_le _) (by omega)
  have ht := h.keep (Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi]) Kt edit) (by decide)
    (by decide) Ot'
  have Mt : val32 t.mem base (numAt len 0) (nw len) = M :=
    Ot.val32 (by omega_using [e04, wbe]) (by omega_using [f5, nw', e04, e45, wbe])
  refine WP.mono (doubleStep_ok ht (by rw [Vt, Mt]; exact Nat.mod_lt _ hM))
    fun u ⟨Ou, Vu, esiu, zu, ediu, Ku⟩ => ?_
  obtain ⟨c₁, c₂⟩ := count1_zf esit hj
  refine ⟨⟨Kt.trans Ku, by rw [ediu, edit], Ot.trans Ou, ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
  rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.pow_succ 2 j, Nat.mul_comm 2 (T * 2 ^ j),
    Nat.mul_assoc]

end VG.Proof.Bignum.X86.PrecomputeRt
