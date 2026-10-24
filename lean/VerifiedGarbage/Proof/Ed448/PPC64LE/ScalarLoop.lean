module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarBit
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.Binary
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448 on PPC64LE: an integer of `N` bytes modulo `L`

`scalarEngine o N` reads the `N` bytes at `r14` from the top, each into the
remainder at `o` bit by bit (`scalarByte_ok`), and leaves the integer modulo
`L` there (`engine_ok`), for bytes that the remainder and its candidate at
`SD` do not overlap.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L decodeLE bytesAt)

/-- Bit `j` of a byte, as `consumeBits` takes it. -/
theorem bit_toNat {w : Nat} (hw : w < 256) (j : Nat) :
    ((BitVec.ofNat 64 w).getLsbD j).toNat = w / 2 ^ j % 2 := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hj : j < 64
  · simp only [hj, decide_true, Bool.true_and, Nat.testBit, Nat.shiftRight_eq_div_pow]
    cases h : w / 2 ^ j % 2 == 1 <;> simp_all <;> omega
  · simp only [hj, decide_false, Bool.false_and, Bool.toNat_false]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : 8 ≤ j)))]

/-- What the scalar code writes: the remainder at `o` and its candidate. -/
abbrev RD (b : Addr) (o : Nat) : List Region := [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 SD, 56⟩]

section
variable {b : Addr}

/-- The bits `js` of the byte in `r16`, in turn. -/
theorem scalarBits_ok {o : Nat} (ho : Rem o) {w : Nat} (hw : w < 256) :
    ∀ (js : List Nat), (∀ j ∈ js, j < 8) → ∀ {s : State}, Ctx b s → (s.gpr .r16).toNat = w →
      V s.mem b o < L →
      WP isa (.block (js.flatMap (scalarBit o))) s fun t =>
        Rest [.r5, .r7, .r8, .r11] s t ∧ Frame (RD b o) s.mem t.mem ∧
        V t.mem b o = js.foldl (fun v j => (2 * v + w / 2 ^ j % 2) % L) (V s.mem b o)
  | [], _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, List.foldl_nil.symm⟩
  | j :: js, hj, s, hc, h16, hr => by
    rw [List.flatMap_cons]
    refine WP.append (scalarBit_ok ho hc hw (hj j List.mem_cons_self) h16 hr) fun t ⟨rt, ft, vt⟩ => ?_
    refine WP.mono (scalarBits_ok ho hw js (fun j h => hj j (List.mem_cons_of_mem _ h))
      (hc.of_rest rt (by decide)) (by rw [rt.gpr _ (by decide), h16])
      (by rw [vt]; exact Nat.mod_lt _ Proof.Ed448.order_pos))
      fun u ⟨ru, fu, vu⟩ => ⟨rt.trans ru, ft.trans fu, by rw [vu, vt]; rfl⟩

/-- One byte: `r15` counted down, the byte at `r14 + r15` into the remainder. -/
theorem scalarByte_ok {o : Nat} (ho : Rem o) {s : State} (hc : Ctx b s) {p : Addr} (h14 : s.gpr .r14 = p)
    {n : Nat} (hn : n + 1 < 2 ^ 15) (h15 : s.gpr .r15 = BitVec.ofNat 64 (n + 1))
    (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 n) 1) (hr : V s.mem b o < L) :
    WP isa (.block (scalarByte o)) s fun t =>
      Rest [.r5, .r7, .r8, .r11, .r15, .r16] s t ∧ Frame (RD b o) s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧
      V t.mem b o = (256 * V s.mem b o + (s.mem (p + BitVec.ofNat 64 n)).toNat) % L := by
  unfold scalarByte scalarRead
  simp only [List.cons_append, List.nil_append]
  refine wp_subi (by decide) (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e15 : s1.gpr .r15 = BitVec.ofNat 64 n := by
    rw [u1.gpr, h15, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
  refine wp_lbz (a := p + BitVec.ofNat 64 n) (by decide) (by decide)
    (by rw [BitVec.add_zero, u2.gpr, u1.other .r14 (by decide), h14, e15])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hin) fun s3 u3 => ?_
  have hr3 : Rest [.r7, .r15, .r16] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hw := (s.mem (p + BitVec.ofNat 64 n)).isLt
  have h16 : (s3.gpr .r16).toNat = (s.mem (p + BitVec.ofNat 64 n)).toNat := by
    rw [u3.gpr, u2.mem, u1.mem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (scalarBits_ok ho hw _ (fun j hj => by simpa using hj) (hc.of_rest hr3 (by decide)) h16
    (by rw [hm3]; exact hr)) fun t ⟨rt, ft, vt⟩ => ⟨(hr3.mono (by decide)).trans (rt.mono (by decide)),
      by rw [hm3] at ft; exact ft, by rw [rt.gpr _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e15], ?_⟩
  rw [vt, hm3]
  obtain ⟨w, hw'⟩ : ∃ w, w = (s.mem (p + BitVec.ofNat 64 n)).toNat := ⟨_, rfl⟩
  rw [← hw'] at hw ⊢
  have e : (fun v j => (2 * v + w / 2 ^ j % 2) % L) =
      fun v j => (2 * v + ((BitVec.ofNat 64 w).getLsbD j).toNat) % L :=
    funext fun v => funext fun j => by rw [bit_toNat hw j]
  rw [e]
  have hc8 := Proof.Ed448.consumeBits_eq (BitVec.ofNat 64 w) 8 (V s.mem b o) hr
  have hw64 : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  rw [hw64, Nat.mod_eq_of_lt (show w < 2 ^ 8 by omega), show (2 : Nat) ^ 8 = 256 from rfl] at hc8
  unfold Proof.Ed448.consumeBits at hc8
  exact hc8

theorem bytesAt_drop (m : Mem) (p : Addr) {N n : Nat} (hn : n < N) :
    (bytesAt m p N).drop n = m (p + BitVec.ofNat 64 n) :: (bytesAt m p N).drop (n + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [bytesAt]; omega)]
  simp [bytesAt]

/-- After the bytes from `n` up: the remainder of the integer they make. -/
structure EngInv (b p : Addr) (o N : Nat) (s0 : State) (n : Nat) (t : State) : Prop where
  le : n ≤ N
  pos : 1 ≤ n
  rest : Rest [.r5, .r7, .r8, .r11, .r15, .r16] s0 t
  frame : Frame (RD b o) s0.mem t.mem
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  val : V t.mem b o = decodeLE ((bytesAt s0.mem p N).drop n) % L

/-- **The `N` bytes at `r14`**, modulo `L`, into the remainder at `o`. -/
theorem engine_ok {o : Nat} (ho : Rem o) {N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 15) {s : State} (hc : Ctx b s)
    {p : Addr} (h14 : s.gpr .r14 = p)
    (hin : ∀ i < N, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (p + BitVec.ofNat 64 i) 1) :
    WP isa (scalarEngine o N) s fun t =>
      Rest [.r5, .r7, .r8, .r11, .r15, .r16] s t ∧ Frame (RD b o) s.mem t.mem ∧
      V t.mem b o = decodeLE (bytesAt s.mem p N) % L := by
  have hf := ho.fits
  unfold scalarEngine
  rw [List.cons_append]
  refine WP.seq (wp_li (by decide) fun s0 u0 => ?_)
  have hc0 : Ctx b s0 := hc.of_rest (u0.rest (ws := [.r7]) (by decide)) (by decide)
  refine WP.append (stores_ok (r := .r7) (o := o) (n := 14) (by omega) hc0) fun s1 ⟨hz, hf1, hg1, hr1⟩ =>
    wp_li (by omega) fun s2 u2 => WP.block_nil ?_
  have iN : EngInv b p o N s N s2 := by
    refine ⟨Nat.le_refl _, hN, (u0.rest (by decide)).trans ((hr1.mono (by decide)).trans (u2.rest (by decide))),
      ?_, u2.gpr, ?_⟩
    · rw [u2.mem, ← u0.mem]; exact hf1.mono fun r hr => by simp [List.mem_singleton.mp hr]
    · have : (bytesAt s.mem p N).drop N = [] := by simp [bytesAt]
      rw [this, u2.mem, V, val32_congr (f := limb s1.mem b o) (g := fun _ => 0) (fun k hk => by
        rw [limb, hz k hk, u0.gpr]; rfl), val32_zero_fn]
      rw [show decodeLE [] = 0 from rfl, Nat.zero_mod]
  refine WP.loop (M := isa) (EngInv b p o N s) ?_ N s2 iN
  intro n t h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := h.pos; omega⟩
  have hk : k < N := by have := h.le; omega
  have hct : Ctx b t := hc.of_rest h.rest (by decide)
  refine WP.mono (scalarByte_ok ho hct (p := p) (by rw [h.rest.gpr _ (by decide), h14]) (by omega) h.r15
    (by rw [h.rest.rd, h.rest.wr]; exact hin k hk)
    (by rw [h.val]; exact Nat.mod_lt _ Proof.Ed448.order_pos)) fun t' ⟨rt, ft, r15, vt⟩ => ?_
  have hb : t.mem (p + BitVec.ofNat 64 k) = s.mem (p + BitVec.ofNat 64 k) :=
    h.frame _ fun r hr => hd k hk r hr
  have hv : V t'.mem b o = decodeLE ((bytesAt s.mem p N).drop k) % L := by
    rw [vt, h.val, hb, bytesAt_drop _ _ hk, Proof.Ed448.reduce_cons]
  have hz : (t'.gpr .r15 != 0) = decide (k ≠ 0) := by rw [r15, ofNat_ne_zero (by omega)]
  rw [eval_nonzero, hz]
  by_cases hk0 : k = 0
  · subst hk0
    refine .inl ⟨by simp, h.rest.trans rt, h.frame.trans ft, ?_⟩
    rw [hv, List.drop_zero]
  · exact .inr ⟨by simp [hk0], k, by omega, ⟨by omega, by omega, h.rest.trans rt, h.frame.trans ft, r15, hv⟩⟩

end

end VG.Proof.Ed448.PPC64LE
