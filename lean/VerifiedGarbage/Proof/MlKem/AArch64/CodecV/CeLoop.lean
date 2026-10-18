module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeSpec

/-!
# ML-KEM on AArch64: the loop of the vector compression

After `k` iterations of a body that compresses `G` groups of a width `w`
(`VInv`): the output's first `w.nb · G · k` bytes are written. The bytes of
a vector stored there (`bytes_write`), and the end (`VInv.done`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- After `k` iterations of `G` groups each, with constants `K` besides those of `cmpV`. -/
structure VInv (w : Width) (G : Nat) (K : State → Prop) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = coeffAddr (fP s₀) (w.c * G * k)
  x2 : s.gpr .x2 = oP s₀ + BitVec.ofNat 64 (w.nb * G * k)
  x11 : (s.gpr .x11).toNat = 256 / (w.c * G) - k
  cs : CConsts w.d s
  K : K s
  out : BytesUpTo s.mem (oP s₀) (32 * w.d) (w.nb * G * k) (L w s₀) (old s₀)
  frame : Frame [oR w s₀] s₀.mem s.mem

/-- The input, from the invariant. -/
theorem VInv.src {w : Width} {G : Nat} {K : State → Prop} {s₀ : State} (hp : Pre w s₀) {k : Nat}
    {s : State} (h : VInv w G K s₀ k s) : Src (fP s₀) (fun i => ((P s₀)[i]!).val) s :=
  ⟨fun i hi => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))),
   fun i hi => hp.coeff h.frame hi⟩

/-- `n` bytes `x` stored at byte `t` of the output. -/
theorem bytes_write {m : Mem} {p : Addr} {N t n : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p N t L old) (hN : N < 2 ^ 32) (hn : t + n ≤ N) {x : BitVec (8 * n)}
    (hx : ∀ i < n, x.extractLsb' (8 * i) 8 = L (t + i)) :
    BytesUpTo (m.write (p + BitVec.ofNat 64 t) n x) p N (t + n) L old := by
  intro j hj
  have d : ((p + BitVec.ofNat 64 j) - (p + BitVec.ofNat 64 t)).toNat =
      if t ≤ j then j - t else 2 ^ 64 + j - t :=
    Offset.sub_toNat' p (by omega) (by omega)
  rw [Mem.write, d]
  by_cases ht : t ≤ j
  · rw [ite_eq_left ht]
    by_cases hnj : j - t < n
    · rw [ite_eq_left hnj, ite_eq_left (by omega), hx _ hnj]
      congr 1; omega
    · rw [ite_eq_right hnj, h j hj, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right ht, ite_eq_right (by omega), h j hj, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- The end of the loop: the whole output. -/
theorem VInv.done {w : Width} {G : Nat} {K : State → Prop} {s₀ s : State}
    (hG : w.nb * G * (256 / (w.c * G)) = 32 * w.d) (h : VInv w G K s₀ (256 / (w.c * G)) s) :
    bytesAt s.mem (oP s₀) (32 * w.d) = Spec.MlKem.compressEncode w.d (P s₀) :=
  (show BytesUpTo _ _ _ (32 * w.d) _ _ from hG ▸ h.out).eq (compressEncode_length _ _) fun _ _ => rfl

/-- The pointer and count updates at the end of a body. -/
theorem tail_ok {w : Width} {G : Nat} {s₀ : State} {k : Nat} (hk : k < 256 / (w.c * G)) {s : State}
    (h0 : s.gpr .x0 = coeffAddr (fP s₀) (w.c * G * k)) (h2 : s.gpr .x2 = oP s₀ + BitVec.ofNat 64 (w.nb * G * k))
    (h11 : (s.gpr .x11).toNat = 256 / (w.c * G) - k) (hi : 4 * (w.c * G) < 4096) (hb : w.nb * G < 4096) :
    WP isa (.block [.addImm .x .x0 .x0 (4 * (w.c * G)), .addImm .x .x2 .x2 (w.nb * G),
      .subImm .x .x11 .x11 1]) s fun t => Only [.x0, .x2, .x11] s t ∧ t.v = s.v ∧
      t.gpr .x0 = coeffAddr (fP s₀) (w.c * G * (k + 1)) ∧
      t.gpr .x2 = oP s₀ + BitVec.ofNat 64 (w.nb * G * (k + 1)) ∧
      (t.gpr .x11).toNat = 256 / (w.c * G) - (k + 1) ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 256 / (w.c * G)) := by
  refine WP.mono (WP.keepV (by simp [writesV]) (wp_addImm hi fun s4 h4 e4 => wp_addImm hb fun s5 h5 e5 =>
    wp_subImm (by decide) fun s6 h6 e6 => wp_nil (Q := fun t => Only [.x0, .x2, .x11] s t ∧
      t.gpr .x0 = coeffAddr (fP s₀) (w.c * G * (k + 1)) ∧
      t.gpr .x2 = oP s₀ + BitVec.ofNat 64 (w.nb * G * (k + 1)) ∧
      (t.gpr .x11).toNat = 256 / (w.c * G) - (k + 1)) ⟨((h4.trans h5).trans h6).mono, ?_, ?_, ?_⟩))
    fun t ⟨⟨o, a, b, c⟩, v⟩ => ⟨o, v, a, b, c, by rw [c]; omega⟩
  · rw [h6.get .x0, h5.get .x0, e4, h0, coeffAddr, coeffAddr, ptr_add]; congr 2; rw [Nat.mul_succ]; omega
  · rw [h6.get .x2, e5, h4.get .x2, h2, ptr_add, Nat.mul_succ]
  · have c : (s5.gpr .x11).toNat = 256 / (w.c * G) - k := by rw [h5.get .x11, h4.get .x11, h11]
    rw [e6, toNat_sub_n (by rw [c]; simp; omega), c]; simp; omega

end VG.Proof.MlKem.AArch64.CE
