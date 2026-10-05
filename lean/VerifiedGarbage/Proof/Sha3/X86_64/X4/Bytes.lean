import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.Sha3.X86_64.X4

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp`. -/
section

/-!
# Keccak-f[1600] four times at once on x86-64: one instruction at a time

Weakest-precondition rules for the AVX2 instructions of `permute4`, in terms
of the four 64-bit elements of each `ymm` register (`q4`), one per state.
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4

/-- Element `k` (`k < 4`) of `ymm r`: lane `j` of state `k`, when `r` holds
lane `j` of the four states. -/
def q4 (s : State) (r : XReg) (k : Nat) : BitVec 64 := qword (s.lane r (k / 2)) (k % 2)

/-! ## Quadwords of values -/

@[simp] theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

@[simp] theorem qword_app1 (a b : BitVec 64) : qword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem qword_xor (x y : BitVec 128) (i : Nat) : qword (x ^^^ y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_or (x y : BitVec 128) (i : Nat) : qword (x ||| y) i = qword x i ||| qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword_andn (x y : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (~~~x &&& y) i = ~~~qword x i &&& qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj, show 64 * i + j < 128 by omega]

theorem qword_psllq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psllq x n) i = qword x i <<< n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem qword_psrlq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq x n) i = qword x i >>> n.toNat := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem mod2_lt (k : Nat) : k % 2 < 2 := Nat.mod_lt _ (by decide)

theorem cases4 {k : Nat} (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem ymm_lane (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    (s.ymm r).extractLsb' (128 * l) 128 = s.lane r l := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hj]

/-- Element `k` of a 256-bit register, as bits of the whole. -/
theorem q4_ymm (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (s.ymm r).extractLsb' (64 * k) 64 = VG.Proof.Sha3.X86_64.X4.q4 s r k := by
  rw [VG.Proof.Sha3.X86_64.X4.q4, ← VG.Proof.Sha3.X86_64.X4.ymm_lane _ _ (show k / 2 < 2 by omega), qword, extract_extract _ _ _ _ _ (by omega)]
  congr 1; omega

/-- A ROTL by `n` as the two shifts. -/
theorem shr_or_shl (v : BitVec 64) {n : Nat} (h₁ : 0 < n) (h₂ : n < 64) :
    v >>> (64 - n) ||| v <<< n = v.rotateRight (64 - n) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt (by omega), show 64 - (64 - n) = n by omega]

/-! ## The machine -/

/-- `s'` is `s` with `ymm d` set to the four elements `v` (flags aside). -/
structure VUpd (s s' : State) (d : XReg) (v : Nat → BitVec 64) : Prop where
  val : ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' d k = v k
  other : ∀ r, r ≠ d → ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' r k = VG.Proof.Sha3.X86_64.X4.q4 s r k
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VUpd.trans {s₁ s₂ s₃ : State} {d : XReg} {v w : Nat → BitVec 64} (h₁ : VG.Proof.Sha3.X86_64.X4.VUpd s₁ s₂ d v)
    (h₂ : VG.Proof.Sha3.X86_64.X4.VUpd s₂ s₃ d w) : VG.Proof.Sha3.X86_64.X4.VUpd s₁ s₃ d w :=
  ⟨h₂.val, fun r h k hk => (h₂.other r h k hk).trans (h₁.other r h k hk), h₂.gpr.trans h₁.gpr,
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem q4_vbin (op : VBinOp) (s : State) (d a b r : XReg) (k : Nat) :
    VG.Proof.Sha3.X86_64.X4.q4 ((VOp.vbin op .l256 d a b).exec s) r k =
      if r = d then qword (op.sse.eval (s.lane a (k / 2)) (s.lane b (k / 2))) (k % 2) else VG.Proof.Sha3.X86_64.X4.q4 s r k := by
  simp only [VG.Proof.Sha3.X86_64.X4.q4, lane_vbin256]
  split <;> rfl

theorem q4_vshift (op : XShiftOp) (s : State) (d a r : XReg) (n : BitVec 8) (k : Nat) :
    VG.Proof.Sha3.X86_64.X4.q4 ((VOp.vshift op .l256 d a n).exec s) r k =
      if r = d then qword (op.eval (s.lane a (k / 2)) n) (k % 2) else VG.Proof.Sha3.X86_64.X4.q4 s r k := by
  simp only [VG.Proof.Sha3.X86_64.X4.q4, lane_vshift256]
  split <;> rfl

theorem VUpd.vbin (op : VBinOp) (s : State) (d a b : XReg) {v : Nat → BitVec 64}
    (hv : ∀ k < 4, qword (op.sse.eval (s.lane a (k / 2)) (s.lane b (k / 2))) (k % 2) = v k) :
    VG.Proof.Sha3.X86_64.X4.VUpd s ((VOp.vbin op .l256 d a b).exec s) d v :=
  ⟨fun k hk => by rw [VG.Proof.Sha3.X86_64.X4.q4_vbin, ite_eq_left rfl]; exact hv k hk,
    fun r hr k _ => by rw [VG.Proof.Sha3.X86_64.X4.q4_vbin, ite_eq_right hr], VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩

theorem VUpd.vshift (op : XShiftOp) (s : State) (d a : XReg) (n : BitVec 8) {v : Nat → BitVec 64}
    (hv : ∀ k < 4, qword (op.eval (s.lane a (k / 2)) n) (k % 2) = v k) :
    VG.Proof.Sha3.X86_64.X4.VUpd s ((VOp.vshift op .l256 d a n).exec s) d v :=
  ⟨fun k hk => by rw [VG.Proof.Sha3.X86_64.X4.q4_vshift, ite_eq_left rfl]; exact hv k hk,
    fun r hr k _ => by rw [VG.Proof.Sha3.X86_64.X4.q4_vshift, ite_eq_right hr], VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vxor {d a b : XReg} (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => VG.Proof.Sha3.X86_64.X4.q4 s a i ^^^ VG.Proof.Sha3.X86_64.X4.q4 s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (vb .vpxor d a b :: is)) s Q :=
  WP.cons rfl (k _ (VUpd.vbin _ _ _ _ _ fun _ _ => by simp only [VBinOp.sse, XBinOp.eval, VG.Proof.Sha3.X86_64.X4.qword_xor]; rfl))

theorem wp_vor {d a b : XReg} (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => VG.Proof.Sha3.X86_64.X4.q4 s a i ||| q4 s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (vb .vpor d a b :: is)) s Q :=
  WP.cons rfl (k _ (VUpd.vbin _ _ _ _ _ fun _ _ => by simp only [VBinOp.sse, XBinOp.eval, VG.Proof.Sha3.X86_64.X4.qword_or]; rfl))

theorem wp_vandn {d a b : XReg}
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => ~~~VG.Proof.Sha3.X86_64.X4.q4 s a i &&& VG.Proof.Sha3.X86_64.X4.q4 s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (vb .vpandn d a b :: is)) s Q :=
  WP.cons rfl (k _ (VUpd.vbin _ _ _ _ _ fun _ _ => by
    simp only [VBinOp.sse, XBinOp.eval]; rw [VG.Proof.Sha3.X86_64.X4.qword_andn _ _ (VG.Proof.Sha3.X86_64.X4.mod2_lt _)]; rfl))

theorem wp_vshl {d a : XReg} {n : Nat} (hn : n < 64)
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => VG.Proof.Sha3.X86_64.X4.q4 s a i <<< n) → WP isa (.block is) s' Q) :
    WP isa (.block (vsh .psllq d a n :: is)) s Q := by
  have e : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  exact WP.cons rfl (k _ (VUpd.vshift _ _ _ _ _ fun _ _ => by
    rw [VG.Proof.Sha3.X86_64.X4.qword_psllq _ (by omega) (VG.Proof.Sha3.X86_64.X4.mod2_lt _), e]; rfl))

theorem wp_vshr {d a : XReg} {n : Nat} (hn : n < 64)
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => VG.Proof.Sha3.X86_64.X4.q4 s a i >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (vsh .psrlq d a n :: is)) s Q := by
  have e : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  exact WP.cons rfl (k _ (VUpd.vshift _ _ _ _ _ fun _ _ => by
    rw [VG.Proof.Sha3.X86_64.X4.qword_psrlq _ (by omega) (VG.Proof.Sha3.X86_64.X4.mod2_lt _), e]; rfl))

theorem wp_vmovq {d : XReg} {g : Reg}
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => if i = 0 then s.gpr g else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vmovq d g) :: is)) s Q := by
  refine WP.cons rfl (k _ ⟨fun i hi => ?_, fun r hr i _ => ?_, VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩)
  · simp only [VOp.exec, VG.Proof.Sha3.X86_64.X4.q4, State.lane_setV128, ite_true]
    rcases VG.Proof.Sha3.X86_64.X4.cases4 hi with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.Sha3.X86_64.X4.qword_app0, VG.Proof.Sha3.X86_64.X4.qword_app1, Nat.reduceDiv, Nat.reduceMod, ite_true, ite_false,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide] <;> simp [qword]
  · simp only [VOp.exec, VG.Proof.Sha3.X86_64.X4.q4, State.lane_setV128, ite_eq_right hr]

theorem wp_vbcast {d a : XReg}
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun _ => VG.Proof.Sha3.X86_64.X4.q4 s a 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastq .l256 d a) :: is)) s Q := by
  refine WP.cons rfl (k _ ⟨fun i hi => ?_, fun r hr i _ => ?_, VOp.exec_gpr _ _, VOp.exec_mem _ _,
    VOp.exec_rd _ _, VOp.exec_wr _ _⟩)
  · simp only [VOp.exec, VG.Proof.Sha3.X86_64.X4.q4, State.lane_setV256, ite_true]
    have : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> split <;> simp [State.lane]
  · simp only [VOp.exec, VG.Proof.Sha3.X86_64.X4.q4, State.lane_setV256, ite_eq_right hr]

theorem wp_vld {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun i => s.mem.readW (a + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l256 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128)
    ((s.mem.readW a 256).extractLsb' 128 128)) (by simp only [exec, ha, State.load256, hin, ite_true,
      Option.map_some]) (k _ ⟨fun i hi => ?_, fun r hr i _ => ?_, by simp, by simp, by simp, by simp⟩)
  · simp only [VG.Proof.Sha3.X86_64.X4.q4, State.lane_setV256, ite_true]
    have e : (if i / 2 = 0 then (s.mem.readW a 256).extractLsb' 0 128 else (s.mem.readW a 256).extractLsb' 128 128) =
        (s.mem.readW a 256).extractLsb' (128 * (i / 2)) 128 := by
      rcases VG.Proof.Sha3.X86_64.X4.cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [e, qword, extract_extract _ _ _ _ _ (by omega),
      show 128 * (i / 2) + 64 * (i % 2) = 8 * (8 * i) by omega]
    exact readW_extract _ _ (k := 8 * i) (n := 8) (by omega)
  · simp only [VG.Proof.Sha3.X86_64.X4.q4, State.lane_setV256, ite_eq_right hr]

theorem wp_vst {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x j, VG.Proof.Sha3.X86_64.X4.q4 s' x j = VG.Proof.Sha3.X86_64.X4.q4 s x j) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

end

/-- Element `k` of a stored register, read back. -/
theorem readW_st (m : Mem) (a : Addr) (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (m.writeW a (s.ymm r)).readW (a + BitVec.ofNat 64 (8 * k)) 64 = VG.Proof.Sha3.X86_64.X4.q4 s r k := by
  have e := readW_writeW_inside m a (s.ymm r) (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * k) = 64 * k by omega, VG.Proof.Sha3.X86_64.X4.q4_ymm _ _ hk] at e
  exact e

end VG.Proof.Sha3.X86_64.X4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.X4.Round`. -/
section

/-!
# Keccak-f[1600] four times at once on x86-64: one round

One round (`round`) of the four interleaved states at `rdi` to those at `rsi`,
lane by lane (`Proof.Sha3.out`) in each of the four elements, and the swap of
`rdi` and `rsi` after it. The proof follows the scalar one
(`Proof/Sha3/X86_64/Permute.lean`).
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3 (C D B out rotl outState)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha3.X86_64 (ea_at wp_mov wp_addi wp_cmp wp_nil)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## The four states in memory -/

/-- Lane `i` of state `k` of the four at `p`. -/
abbrev la (p : Addr) (i k : Nat) : Addr := p + BitVec.ofNat 64 (32 * i + 8 * k)

/-- The four states at `p` hold `A 0`, …, `A 3`. -/
def Lanes4 (m : Mem) (p : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) : Prop :=
  ∀ i < 25, ∀ k < 4, m.readW (VG.Proof.Sha3.X86_64.X4.la p i k) 64 = (A k)[i]!

theorem la_eq (p : Addr) (i k : Nat) :
    p + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 (8 * k) = VG.Proof.Sha3.X86_64.X4.la p i k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Where a round reads and writes: the states at `src`, the round constant
at `rcp`, and the states at `dst`, which overlap neither. -/
structure Env (rd wr : List Region) (src dst rcp : Addr) : Prop where
  src_in : ∀ i < 25, InRegions (rd ++ wr) (src + BitVec.ofNat 64 (32 * i)) 32
  dst_out : ∀ i < 25, InRegions wr (dst + BitVec.ofNat 64 (32 * i)) 32
  rc_in : InRegions (rd ++ wr) rcp 32
  dst_src : Region.Disjoint ⟨dst, 800⟩ ⟨src, 800⟩
  dst_rc : Region.Disjoint ⟨dst, 800⟩ ⟨rcp, 32⟩

theorem la_contains (p : Addr) {i k : Nat} (hi : i < 25) (hk : k < 4) :
    (⟨p, 800⟩ : Region).Contains (VG.Proof.Sha3.X86_64.X4.la p i k) (64 / 8) :=
  Offset.contains_base p (by omega) (by omega)

theorem Env.src_frame {rd wr : List Region} {src dst rcp : Addr} (h : VG.Proof.Sha3.X86_64.X4.Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 800⟩] m m') {i k : Nat} (hi : i < 25) (hk : k < 4) :
    m'.readW (VG.Proof.Sha3.X86_64.X4.la src i k) 64 = m.readW (VG.Proof.Sha3.X86_64.X4.la src i k) 64 :=
  hf.readW (VG.Proof.Sha3.X86_64.X4.la_contains src hi hk) (by simpa using h.dst_src.symm) (by decide)

theorem Env.rc_frame {rd wr : List Region} {src dst rcp : Addr} (h : VG.Proof.Sha3.X86_64.X4.Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 800⟩] m m') {k : Nat} (hk : k < 4) :
    m'.readW (VG.Proof.Sha3.X86_64.X4.la rcp 0 k) 64 = m.readW (VG.Proof.Sha3.X86_64.X4.la rcp 0 k) 64 :=
  hf.readW (Offset.contains_base rcp (show 32 * 0 + 8 * k + 64 / 8 ≤ 32 by omega) (by omega))
    (by simpa using h.dst_rc.symm) (by decide)

/-! ## Registers -/

theorem creg_inj : ∀ x < 5, ∀ x' < 5, creg x = creg x' → x = x' := by decide
theorem dreg_inj : ∀ x < 5, ∀ x' < 5, dreg x = dreg x' → x = x' := by decide
theorem creg_dreg : ∀ x < 5, ∀ x' < 5, creg x ≠ dreg x' := by decide
theorem T_creg : ∀ x < 5, T ≠ creg x := by decide
theorem T_dreg : ∀ x < 5, T ≠ dreg x := by decide
theorem U_creg : ∀ x < 5, U ≠ creg x := by decide
theorem U_dreg : ∀ x < 5, U ≠ dreg x := by decide
theorem T_U : T ≠ U := by decide

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : creg x' ≠ creg x :=
  fun e => h (VG.Proof.Sha3.X86_64.X4.creg_inj x' hx' x hx e)

theorem dreg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : dreg x' ≠ dreg x :=
  fun e => h (VG.Proof.Sha3.X86_64.X4.dreg_inj x' hx' x hx e)

/-! ## Vector code -/

/-- `s'` differs from `s` only in the vector registers `ws` (and the flags). -/
structure VW (s s' : State) (ws : List XReg) : Prop where
  other : ∀ r, r ∉ ws → ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' r k = VG.Proof.Sha3.X86_64.X4.q4 s r k
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VW.refl (s : State) (ws : List XReg) : VG.Proof.Sha3.X86_64.X4.VW s s ws := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem VW.trans {s₁ s₂ s₃ : State} {ws : List XReg} (h₁ : VG.Proof.Sha3.X86_64.X4.VW s₁ s₂ ws) (h₂ : VG.Proof.Sha3.X86_64.X4.VW s₂ s₃ ws) : VG.Proof.Sha3.X86_64.X4.VW s₁ s₃ ws :=
  ⟨fun r h k hk => (h₂.other r h k hk).trans (h₁.other r h k hk), h₂.gpr.trans h₁.gpr,
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem VUpd.vw {s s' : State} {d : XReg} {v : Nat → BitVec 64} (h : VG.Proof.Sha3.X86_64.X4.VUpd s s' d v) {ws : List XReg}
    (hd : d ∈ ws) : VG.Proof.Sha3.X86_64.X4.VW s s' ws :=
  ⟨fun r hr k hk => h.other r (fun e => hr (e ▸ hd)) k hk, h.gpr, h.mem, h.rd, h.wr⟩

theorem VW.upd {s₀ s s' : State} {ws : List XReg} (h : VG.Proof.Sha3.X86_64.X4.VW s₀ s ws) {d : XReg} {v : Nat → BitVec 64}
    (u : VG.Proof.Sha3.X86_64.X4.VUpd s s' d v) (hd : d ∈ ws) : VG.Proof.Sha3.X86_64.X4.VW s₀ s' ws := h.trans (u.vw hd)

/-- A load of lane `i` of the four states at `p` (`= b`), as they were at `s₀`. -/
theorem wp_ld {is : List Instr} {Q : State → Prop} {s₀ s : State} {ws : List XReg} (h : VG.Proof.Sha3.X86_64.X4.VW s₀ s ws)
    {b : Reg} {p : Addr} {i : Nat} {d : XReg} (hb : s₀.gpr b = p)
    (hin : InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 (32 * i)) 32)
    (k : ∀ s', VG.Proof.Sha3.X86_64.X4.VUpd s s' d (fun k => s₀.mem.readW (VG.Proof.Sha3.X86_64.X4.la p i k) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (ld d b i :: is)) s Q :=
  VG.Proof.Sha3.X86_64.X4.wp_vld (by rw [ea_at, h.gpr, hb]) (by rw [h.rd, h.wr]; exact hin) fun s' u =>
    k s' ⟨fun j hj => by rw [u.val j hj, h.mem, VG.Proof.Sha3.X86_64.X4.la_eq], u.other, u.gpr, u.mem, u.rd, u.wr⟩

/-! ## θ -/

/-- What the round reads before it writes: the states at `src`. -/
structure Src (s : State) (src : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) : Prop where
  rdi : s.gpr .rdi = src
  src_in : ∀ i < 25, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (32 * i)) 32
  lanes : VG.Proof.Sha3.X86_64.X4.Lanes4 s.mem src A

theorem Src.vw {s s' : State} {src : Addr} {A : Nat → VG.Proof.Sha3.X86_64.X4.KState} (h : VG.Proof.Sha3.X86_64.X4.Src s src A) {ws : List XReg}
    (hw : VG.Proof.Sha3.X86_64.X4.VW s s' ws) : VG.Proof.Sha3.X86_64.X4.Src s' src A :=
  ⟨by rw [hw.gpr, h.rdi], by rw [hw.rd, hw.wr]; exact h.src_in, by rw [hw.mem]; exact h.lanes⟩

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (src : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (hs : VG.Proof.Sha3.X86_64.X4.Src s src A) :
    WP isa (.block (column x)) s fun s' =>
      VG.Proof.Sha3.X86_64.X4.VW s s' [creg x, T] ∧ ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' (creg x) k = C (A k) x := by
  have cT : creg x ≠ T := (VG.Proof.Sha3.X86_64.X4.T_creg x hx).symm
  have m₁ : creg x ∈ [creg x, T] := by simp
  have m₂ : T ∈ [creg x, T] := by simp
  have w₀ := VW.refl s [creg x, T]
  unfold column
  refine VG.Proof.Sha3.X86_64.X4.wp_ld w₀ hs.rdi (hs.src_in _ (by omega)) fun s₁ u₁ => ?_
  have w₁ := w₀.upd u₁ m₁
  refine VG.Proof.Sha3.X86_64.X4.wp_ld w₁ hs.rdi (hs.src_in _ (by omega)) fun s₂ u₂ => ?_
  have w₂ := w₁.upd u₂ m₂
  refine VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₃ u₃ => ?_
  have w₃ := w₂.upd u₃ m₁
  refine VG.Proof.Sha3.X86_64.X4.wp_ld w₃ hs.rdi (hs.src_in _ (by omega)) fun s₄ u₄ => ?_
  have w₄ := w₃.upd u₄ m₂
  refine VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₅ u₅ => ?_
  have w₅ := w₄.upd u₅ m₁
  refine VG.Proof.Sha3.X86_64.X4.wp_ld w₅ hs.rdi (hs.src_in _ (by omega)) fun s₆ u₆ => ?_
  have w₆ := w₅.upd u₆ m₂
  refine VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₇ u₇ => ?_
  have w₇ := w₆.upd u₇ m₁
  refine VG.Proof.Sha3.X86_64.X4.wp_ld w₇ hs.rdi (hs.src_in _ (by omega)) fun s₈ u₈ => ?_
  have w₈ := w₇.upd u₈ m₂
  refine VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₉ u₉ => wp_nil ⟨w₈.upd u₉ m₁, fun k hk => ?_⟩
  simp only [u₉.val k hk, u₈.val k hk, u₈.other _ cT k hk, u₇.val k hk, u₆.val k hk, u₆.other _ cT k hk,
    u₅.val k hk, u₄.val k hk, u₄.other _ cT k hk, u₃.val k hk, u₂.val k hk, u₂.other _ cT k hk,
    u₁.val k hk, hs.lanes x (by omega) k hk, hs.lanes (x + 5) (by omega) k hk,
    hs.lanes (x + 10) (by omega) k hk, hs.lanes (x + 15) (by omega) k hk, hs.lanes (x + 20) (by omega) k hk]
  rfl

/-- `s'` agrees with `s` but for the vector registers and the flags. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Same.refl (s : State) : VG.Proof.Sha3.X86_64.X4.Same s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Sha3.X86_64.X4.Same s₁ s₂) (h₂ : VG.Proof.Sha3.X86_64.X4.Same s₂ s₃) : VG.Proof.Sha3.X86_64.X4.Same s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem VW.same {s s' : State} {ws : List XReg} (h : VG.Proof.Sha3.X86_64.X4.VW s s' ws) : VG.Proof.Sha3.X86_64.X4.Same s s' := ⟨h.gpr, h.mem, h.rd, h.wr⟩

theorem Src.same {s s' : State} {src : Addr} {A : Nat → VG.Proof.Sha3.X86_64.X4.KState} (h : VG.Proof.Sha3.X86_64.X4.Src s src A) (hw : VG.Proof.Sha3.X86_64.X4.Same s s') :
    VG.Proof.Sha3.X86_64.X4.Src s' src A :=
  ⟨by rw [hw.gpr, h.rdi], by rw [hw.rd, hw.wr]; exact h.src_in, by rw [hw.mem]; exact h.lanes⟩

/-- After the first `n` columns. -/
def ColInv (s₀ : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (n : Nat) (s : State) : Prop :=
  VG.Proof.Sha3.X86_64.X4.Same s₀ s ∧ ∀ x < n, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (creg x) k = C (A k) x

theorem columns_ok (s₀ : State) (src : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (hs : VG.Proof.Sha3.X86_64.X4.Src s₀ src A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (VG.Proof.Sha3.X86_64.X4.ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.X86_64.X4.ColInv s₀ A) (fun x s hx ⟨hw, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.column_ok x hx s src A (hs.same hw)) fun s' ⟨h, hv⟩ => ⟨hw.trans h.same, fun x' hx' k hk => ?_⟩
  by_cases e : x' = x
  · subst e; exact hv k hk
  · rw [h.other _ (by simpa using ⟨VG.Proof.Sha3.X86_64.X4.creg_ne hx (by omega) e, (VG.Proof.Sha3.X86_64.X4.T_creg x' (by omega)).symm⟩) k hk,
      hc x' (by omega) k hk]

/-! ## D -/

theorem rotr63 (v : BitVec 64) : v <<< 1 ||| v >>> 63 = v.rotateRight 63 := by
  have := VG.Proof.Sha3.X86_64.X4.shr_or_shl v (n := 1) (by decide) (by decide)
  rwa [BitVec.or_comm] at this

theorem dcol_ok (x : Nat) (_hx : x < 5) (s : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState)
    (hc : ∀ x' < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (creg x') k = C (A k) x') :
    WP isa (.block (dcol x)) s fun s' =>
      VG.Proof.Sha3.X86_64.X4.VW s s' [T, U, dreg x] ∧ ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' (dreg x) k = D (A k) x := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  have w₀ := VW.refl s [T, U, dreg x]
  unfold dcol
  refine VG.Proof.Sha3.X86_64.X4.wp_vshl (by decide) fun s₁ u₁ => VG.Proof.Sha3.X86_64.X4.wp_vshr (by decide) fun s₂ u₂ => VG.Proof.Sha3.X86_64.X4.wp_vor fun s₃ u₃ =>
    VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₄ u₄ => wp_nil ⟨(((w₀.upd u₁ (by simp)).upd u₂ (by simp)).upd u₃ (by simp)).upd u₄ (by simp),
      fun k hk => ?_⟩
  simp only [u₄.val k hk, u₃.val k hk, u₃.other _ (VG.Proof.Sha3.X86_64.X4.T_creg _ h4).symm k hk, u₂.other _ VG.Proof.Sha3.X86_64.X4.T_U k hk,
    u₂.val k hk, u₂.other _ (VG.Proof.Sha3.X86_64.X4.U_creg _ h4).symm k hk, u₁.val k hk, u₁.other _ (VG.Proof.Sha3.X86_64.X4.T_creg _ h1).symm k hk,
    u₁.other _ (VG.Proof.Sha3.X86_64.X4.T_creg _ h4).symm k hk, hc _ h1 k hk, hc _ h4 k hk, VG.Proof.Sha3.X86_64.X4.rotr63]
  rfl

/-- After the first `n` of the `D[x]`. -/
def DInv (s₀ : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (n : Nat) (s : State) : Prop :=
  VG.Proof.Sha3.X86_64.X4.Same s₀ s ∧ (∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (creg x) k = C (A k) x) ∧ ∀ x < n, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (dreg x) k = D (A k) x

theorem dcols_ok (s₀ : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (hc : ∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s₀ (creg x) k = C (A k) x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (VG.Proof.Sha3.X86_64.X4.DInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.X86_64.X4.DInv s₀ A) (fun x s hx ⟨hw, hcs, hd⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hc, fun _ h => absurd h (by omega)⟩
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.dcol_ok x hx s A hcs) fun s' ⟨h, hv⟩ => ⟨hw.trans h.same, fun x' hx' k hk => ?_, fun x' hx' k hk => ?_⟩
  · rw [h.other _ (by simpa using ⟨(VG.Proof.Sha3.X86_64.X4.T_creg x' hx').symm, (VG.Proof.Sha3.X86_64.X4.U_creg x' hx').symm, VG.Proof.Sha3.X86_64.X4.creg_dreg x' hx' x hx⟩) k hk,
      hcs x' hx' k hk]
  · by_cases e : x' = x
    · subst e; exact hv k hk
    · rw [h.other _ (by simpa using ⟨(VG.Proof.Sha3.X86_64.X4.T_dreg x' (by omega)).symm, (VG.Proof.Sha3.X86_64.X4.U_dreg x' (by omega)).symm,
          VG.Proof.Sha3.X86_64.X4.dreg_ne hx (by omega) e⟩) k hk,
        hd x' (by omega) k hk]

/-! ## A plane -/

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) (s : State) (src : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState)
    (hs : VG.Proof.Sha3.X86_64.X4.Src s src A) (hd : ∀ x' < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (dreg x') k = D (A k) x') :
    WP isa (.block (laneB x y)) s fun s' =>
      VG.Proof.Sha3.X86_64.X4.VW s s' [creg x, T] ∧ ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' (creg x) k = B (A k) x y := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk5 : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  have cT : creg x ≠ T := (VG.Proof.Sha3.X86_64.X4.T_creg x hx).symm
  have w₀ := VW.refl s [creg x, T]
  unfold laneB
  rw [List.cons_append, List.cons_append]
  refine VG.Proof.Sha3.X86_64.X4.wp_ld w₀ hs.rdi (hs.src_in _ hj) fun s₁ u₁ => VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₂ u₂ => ?_
  have w₂ := (w₀.upd u₁ (by simp)).upd u₂ (by simp)
  have hv : ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s₂ (creg x) k = (A k)[piSrc x y]! ^^^ D (A k) ((x + 3 * y) % 5) := fun k hk => by
    simp only [u₂.val k hk, u₁.val k hk, u₁.other _ (VG.Proof.Sha3.X86_64.X4.creg_dreg x hx _ hk5).symm k hk, hd _ hk5 k hk,
      hs.lanes _ hj k hk]
  split
  · rename_i h0
    refine wp_nil ⟨w₂, fun k hk => ?_⟩
    rw [hv k hk, B, rotl, h0, ite_eq_left rfl]
  · rename_i h0
    have hr := Proof.Sha3.rhoOff_lt _ hj
    refine VG.Proof.Sha3.X86_64.X4.wp_vshl hr fun s₃ u₃ => VG.Proof.Sha3.X86_64.X4.wp_vshr (by omega) fun s₄ u₄ => VG.Proof.Sha3.X86_64.X4.wp_vor fun s₅ u₅ =>
      wp_nil ⟨((w₂.upd u₃ (by simp)).upd u₄ (by simp)).upd u₅ (by simp), fun k hk => ?_⟩
    simp only [u₅.val k hk, u₄.val k hk, u₄.other _ cT.symm k hk, u₃.val k hk, u₃.other _ cT k hk, hv k hk]
    rw [VG.Proof.Sha3.X86_64.X4.shr_or_shl _ (by omega) hr, B, rotl, ite_eq_right h0]

/-- After the first `n` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (y n : Nat) (s : State) : Prop :=
  VG.Proof.Sha3.X86_64.X4.Same s₀ s ∧ (∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (dreg x) k = D (A k) x) ∧ ∀ x < n, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (creg x) k = B (A k) x y

theorem laneBs_ok (y : Nat) (hy : y < 5) (s₀ : State) (src : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (hs : VG.Proof.Sha3.X86_64.X4.Src s₀ src A)
    (hd : ∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s₀ (dreg x) k = D (A k) x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB x y)) s₀ (VG.Proof.Sha3.X86_64.X4.BInv s₀ A y 5) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.X86_64.X4.BInv s₀ A y) (fun x s hx ⟨hw, hds, hb⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hd, fun _ h => absurd h (by omega)⟩
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.laneB_ok x y hx hy s src A (hs.same hw) hds) fun s' ⟨h, hv⟩ =>
    ⟨hw.trans h.same, fun x' hx' k hk => ?_, fun x' hx' k hk => ?_⟩
  · rw [h.other _ (by simpa using ⟨(VG.Proof.Sha3.X86_64.X4.creg_dreg x hx x' hx').symm, (VG.Proof.Sha3.X86_64.X4.T_dreg x' hx').symm⟩) k hk, hds x' hx' k hk]
  · by_cases e : x' = x
    · subst e; exact hv k hk
    · rw [h.other _ (by simpa using ⟨VG.Proof.Sha3.X86_64.X4.creg_ne hx (by omega) e, (VG.Proof.Sha3.X86_64.X4.T_creg x' (by omega)).symm⟩) k hk,
        hb x' (by omega) k hk]

theorem not_eq_xor (v : VG.Proof.Sha3.X86_64.X4.Lane) : ~~~v = v ^^^ 0xffffffffffffffff := by
  rw [BitVec.xor_comm]; rfl

/-- The 64-bit element `k` of a 256-bit write, read back. -/
theorem readW_write256 (m : Mem) (a : Addr) (v : BitVec 256) {k : Nat} (hk : k < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * k)) 64 = v.extractLsb' (64 * k) 64 := by
  have e := readW_writeW_inside m a v (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * k) = 64 * k by omega] at e
  exact e

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) (s : State) (dst rcp : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState)
    (rc : VG.Proof.Sha3.X86_64.X4.Lane) (hrsi : s.gpr .rsi = dst) (hrdx : s.gpr .rdx = rcp)
    (hout : InRegions s.wr (dst + BitVec.ofNat 64 (32 * (x + 5 * y))) 32)
    (hrc_in : InRegions (s.rd ++ s.wr) (rcp + BitVec.ofNat 64 (32 * 0)) 32)
    (hrc : ∀ k < 4, s.mem.readW (VG.Proof.Sha3.X86_64.X4.la rcp 0 k) 64 = rc)
    (hb : ∀ x' < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (creg x') k = B (A k) x' y) :
    WP isa (.block (chi x y)) s fun s' =>
      s'.gpr = s.gpr ∧ (∀ r, r ≠ T → r ≠ U → ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' r k = VG.Proof.Sha3.X86_64.X4.q4 s r k) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∃ v : BitVec 256, s'.mem = s.mem.writeW (dst + BitVec.ofNat 64 (32 * (x + 5 * y))) v ∧
        ∀ k < 4, v.extractLsb' (64 * k) 64 = out (A k) rc x y := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have w₀ := VW.refl s [T, U]
  unfold chi
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Sha3.X86_64.X4.wp_vandn fun s₁ u₁ => VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₂ u₂ => ?_
  have w₂ := (w₀.upd u₁ (by simp)).upd u₂ (by simp)
  have ht : ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s₂ T k = (B (A k) ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B (A k) ((x + 2) % 5) y ^^^
      B (A k) x y := fun k hk => by
    simp only [u₂.val k hk, u₁.val k hk, u₁.other _ (VG.Proof.Sha3.X86_64.X4.T_creg _ hx).symm k hk, hb _ h1 k hk, hb _ h2 k hk,
      hb _ hx k hk, VG.Proof.Sha3.X86_64.X4.not_eq_xor]
  -- The store, from a state that differs from `s` only in `T` and `U`.
  have fin : ∀ s₅ : State, VG.Proof.Sha3.X86_64.X4.VW s s₅ [T, U] → (∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s₅ T k = out (A k) rc x y) →
      WP isa (.block [Impl.Sha3.X86_64.X4.st .rsi (x + 5 * y) T]) s₅ fun s' =>
        s'.gpr = s.gpr ∧ (∀ r, r ≠ T → r ≠ U → ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s' r k = VG.Proof.Sha3.X86_64.X4.q4 s r k) ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ ∃ v : BitVec 256, s'.mem = s.mem.writeW (dst + BitVec.ofNat 64 (32 * (x + 5 * y))) v ∧
          ∀ k < 4, v.extractLsb' (64 * k) 64 = out (A k) rc x y := fun s₅ h₅ hv => by
    refine VG.Proof.Sha3.X86_64.X4.wp_vst (by rw [ea_at, h₅.gpr, hrsi]) (by rw [h₅.wr]; exact hout) fun s₆ g₆ q₆ m₆ r₆ w₆ => wp_nil ?_
    refine ⟨by rw [g₆, h₅.gpr], fun r h₁ h₂ k hk => by rw [q₆, h₅.other r (by simp [h₁, h₂]) k hk],
      by rw [r₆, h₅.rd], by rw [w₆, h₅.wr], s₅.ymm T, by rw [m₆, h₅.mem], fun k hk => ?_⟩
    rw [VG.Proof.Sha3.X86_64.X4.q4_ymm _ _ hk, hv k hk]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [and_self, ite_true, List.cons_append, List.nil_append]
    refine VG.Proof.Sha3.X86_64.X4.wp_ld w₂ hrdx hrc_in fun s₃ u₃ => VG.Proof.Sha3.X86_64.X4.wp_vxor fun s₄ u₄ => ?_
    refine fin s₄ ((w₂.upd u₃ (by simp)).upd u₄ (by simp)) fun k hk => ?_
    simp only [u₄.val k hk, u₃.val k hk, u₃.other _ VG.Proof.Sha3.X86_64.X4.T_U k hk, ht k hk, hrc k hk, out, and_self, ite_true]
  · simp only [h0, ite_false, List.nil_append]
    refine fin s₂ w₂ fun k hk => ?_
    rw [ht k hk, out]
    simp only [h0, ite_false]

/-- After `n` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (rc : VG.Proof.Sha3.X86_64.X4.Lane) (dst : Addr) (y n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨dst, 800⟩] s₀.mem s.mem
  dregs : ∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (dreg x) k = D (A k) x
  bregs : ∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (creg x) k = B (A k) x y
  lanes : ∀ j < 5 * y + n, ∀ k < 4, s.mem.readW (VG.Proof.Sha3.X86_64.X4.la dst j k) 64 = out (A k) rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) (s₀ : State) (src dst rcp : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (rc : VG.Proof.Sha3.X86_64.X4.Lane)
    (he : VG.Proof.Sha3.X86_64.X4.Env s₀.rd s₀.wr src dst rcp) (hrsi : s₀.gpr .rsi = dst) (hrdx : s₀.gpr .rdx = rcp)
    (hrc : ∀ k < 4, s₀.mem.readW (VG.Proof.Sha3.X86_64.X4.la rcp 0 k) 64 = rc) (s : State) (hs : VG.Proof.Sha3.X86_64.X4.ChiInv s₀ A rc dst y 0 s) :
    WP isa (.block ((List.range 5).flatMap fun x => chi x y)) s (VG.Proof.Sha3.X86_64.X4.ChiInv s₀ A rc dst y 5) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.X86_64.X4.ChiInv s₀ A rc dst y) (fun x s hx hi => ?_) 5 (Nat.le_refl _) s hs
  have hj : x + 5 * y < 25 := by omega
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.chi_ok x y hx hy s dst rcp A rc (by rw [hi.gpr, hrsi]) (by rw [hi.gpr, hrdx])
    (by rw [hi.wr]; exact he.dst_out _ hj) (by rw [hi.rd, hi.wr]; simpa using he.rc_in)
    (fun k hk => by rw [he.rc_frame hi.frame hk, hrc k hk]) hi.bregs)
    fun s' ⟨hg, hq, hrd, hwr, v, hm, hv⟩ => ?_
  refine ⟨hg.trans hi.gpr, hrd.trans hi.rd, hwr.trans hi.wr, ?_,
    fun x' hx' k hk => by rw [hq _ (VG.Proof.Sha3.X86_64.X4.T_dreg x' hx').symm (VG.Proof.Sha3.X86_64.X4.U_dreg x' hx').symm k hk, hi.dregs x' hx' k hk],
    fun x' hx' k hk => by rw [hq _ (VG.Proof.Sha3.X86_64.X4.T_creg x' hx').symm (VG.Proof.Sha3.X86_64.X4.U_creg x' hx').symm k hk, hi.bregs x' hx' k hk],
    fun j hj' k hk => ?_⟩
  · rw [hm]; exact hi.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base dst (by omega) (by omega))
  · rw [hm]
    by_cases e : j = x + 5 * y
    · subst e
      rw [← VG.Proof.Sha3.X86_64.X4.la_eq, VG.Proof.Sha3.X86_64.X4.readW_write256 _ _ _ hk, hv k hk, show (x + 5 * y) % 5 = x by omega,
        show (x + 5 * y) / 5 = y by omega]
    · have := readW_writeW_off s.mem dst v (d := 32 * j + 8 * k) (e := 32 * (x + 5 * y)) (n := 8)
        (by omega) (by omega) (by omega)
      rw [this]
      exact hi.lanes j (by omega) k hk

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (rc : VG.Proof.Sha3.X86_64.X4.Lane) (dst : Addr) (y : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨dst, 800⟩] s₀.mem s.mem
  dregs : ∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s (dreg x) k = D (A k) x
  lanes : ∀ j < 5 * y, ∀ k < 4, s.mem.readW (VG.Proof.Sha3.X86_64.X4.la dst j k) 64 = out (A k) rc (j % 5) (j / 5)

theorem planes_ok (s₀ : State) (src dst rcp : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (rc : VG.Proof.Sha3.X86_64.X4.Lane)
    (he : VG.Proof.Sha3.X86_64.X4.Env s₀.rd s₀.wr src dst rcp) (hrdi : s₀.gpr .rdi = src) (hrsi : s₀.gpr .rsi = dst)
    (hrdx : s₀.gpr .rdx = rcp) (hA : VG.Proof.Sha3.X86_64.X4.Lanes4 s₀.mem src A) (hrc : ∀ k < 4, s₀.mem.readW (VG.Proof.Sha3.X86_64.X4.la rcp 0 k) 64 = rc)
    (hd : ∀ x < 5, ∀ k < 4, VG.Proof.Sha3.X86_64.X4.q4 s₀ (dreg x) k = D (A k) x) :
    WP isa (.block ((List.range 5).flatMap plane)) s₀ (VG.Proof.Sha3.X86_64.X4.PInv s₀ A rc dst 5) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.X86_64.X4.PInv s₀ A rc dst) (fun y s hy hi => ?_) 5 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, hd, fun _ h => absurd h (by omega)⟩
  unfold plane
  rw [WP.block_append_iff]
  have hs : VG.Proof.Sha3.X86_64.X4.Src s src A := ⟨by rw [hi.gpr, hrdi], by rw [hi.rd, hi.wr]; exact he.src_in,
    fun i hi' k hk => by rw [he.src_frame hi.frame hi' hk, hA i hi' k hk]⟩
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.laneBs_ok y hy s src A hs hi.dregs) fun s₁ ⟨hw, hds, hb⟩ => ?_
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.chis_ok y hy s₀ src dst rcp A rc he hrsi hrdx hrc s₁
    ⟨hw.gpr.trans hi.gpr, hw.rd.trans hi.rd, hw.wr.trans hi.wr, by rw [hw.mem]; exact hi.frame, hds, hb,
      fun j hj k hk => by rw [hw.mem]; exact hi.lanes j hj k hk⟩)
    fun s₂ h₂ => ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.frame, h₂.dregs, fun j hj => h₂.lanes j (by omega)⟩

/-! ## The round -/

theorem tail_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rax),
      .alu .add .rdx (.imm 32), .alu .cmp .rdx (.reg .rcx)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .rdi ∧ s'.gpr .rdx = s.gpr .rdx + 32 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (s.gpr .rdx + 32 - s.gpr .rcx == 0) := by
  refine wp_mov fun s₁ h₁ => wp_mov fun s₂ h₂ => wp_mov fun s₃ h₃ => wp_addi fun s₄ h₄ =>
    wp_cmp fun s₅ g₅ m₅ r₅ w₅ _ z₅ => wp_nil ?_
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = (32 : BitVec 64) := by decide
  have dx : s₄.gpr .rdx = s.gpr .rdx + 32 := by
    rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), e32]
  have cx : s₄.gpr .rcx = s.gpr .rcx := by
    rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  exact ⟨by rw [g₅, h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)],
    by rw [g₅, h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.gpr], by rw [g₅, dx],
    fun r ra rdi rsi rdx => by rw [g₅, h₄.other r rdx, h₃.other r rsi, h₂.other r rdi, h₁.other r ra],
    by rw [m₅, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [r₅, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
    by rw [w₅, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [z₅, dx, cx]⟩

theorem round_ok (s : State) (src dst rcp : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (rc : VG.Proof.Sha3.X86_64.X4.Lane)
    (he : VG.Proof.Sha3.X86_64.X4.Env s.rd s.wr src dst rcp) (hrdi : s.gpr .rdi = src) (hrsi : s.gpr .rsi = dst)
    (hrdx : s.gpr .rdx = rcp) (hA : VG.Proof.Sha3.X86_64.X4.Lanes4 s.mem src A) (hrc : ∀ k < 4, s.mem.readW (VG.Proof.Sha3.X86_64.X4.la rcp 0 k) 64 = rc) :
    WP isa (.block round) s fun s' =>
      VG.Proof.Sha3.X86_64.X4.Lanes4 s'.mem dst (fun k => outState (A k) rc) ∧ Frame [⟨dst, 800⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rdi = dst ∧ s'.gpr .rsi = src ∧ s'.gpr .rdx = rcp + 32 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.zf = some (rcp + 32 - s.gpr .rcx == 0) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.columns_ok s src A ⟨hrdi, he.src_in, hA⟩) fun s₁ ⟨k₁, c₁⟩ => ?_
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.dcols_ok s₁ A c₁) fun s₂ ⟨k₂, _, d₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.planes_ok s₂ src dst rcp A rc (by rw [k₁₂.rd, k₁₂.wr]; exact he)
    (by rw [k₁₂.gpr, hrdi]) (by rw [k₁₂.gpr, hrsi]) (by rw [k₁₂.gpr, hrdx]) (by rw [k₁₂.mem]; exact hA)
    (by rw [k₁₂.mem]; exact hrc) d₂) fun s₃ h₃ => ?_
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.tail_ok s₃) fun s₄ ⟨e₁, e₂, e₃, e₄, e₆, e₇, e₈, e₉⟩ => ?_
  have hg : s₃.gpr = s.gpr := h₃.gpr.trans k₁₂.gpr
  refine ⟨fun i hi k hk => ?_, by rw [e₆, ← k₁₂.mem]; exact h₃.frame, by rw [e₇, h₃.rd, k₁₂.rd],
    by rw [e₈, h₃.wr, k₁₂.wr], by rw [e₁, hg, hrsi], by rw [e₂, hg, hrdi], by rw [e₃, hg, hrdx],
    fun r a b c d => by rw [e₄ r a b c d, hg], by rw [e₉, hg, hrdx]⟩
  rw [e₆, h₃.lanes i (by omega) k hk]
  simp [outState, hi]

end VG.Proof.Sha3.X86_64.X4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.X4.Loop`. -/
section

/-!
# Keccak-f[1600] four times at once on x86-64: the 24 rounds

`permute4` applies Keccak-f[1600] to each of the four interleaved states at
`rdi`, using the 800 bytes at `rsi` for every other round and the table of
round constants at `rdx` (`permute4_ok`).
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4
open VG.Spec.Sha3 (keccakF rnd RC)
open VG.Proof.Sha3 (outState outState_eq foldl_succ)

/-- Where `permute4` reads and writes: the four states at `src`, the 800
bytes at `oth`, and the table at `tbl`, none of which overlap, and the
round constants in the table. -/
structure Pre4 (s₀ : State) (src oth tbl : Addr) : Prop where
  src_in : ∀ i < 25, InRegions s₀.wr (src + BitVec.ofNat 64 (32 * i)) 32
  oth_in : ∀ i < 25, InRegions s₀.wr (oth + BitVec.ofNat 64 (32 * i)) 32
  tbl_in : ∀ r < 24, InRegions (s₀.rd ++ s₀.wr) (tbl + BitVec.ofNat 64 (32 * r)) 32
  src_oth : Region.Disjoint ⟨src, 800⟩ ⟨oth, 800⟩
  src_tbl : Region.Disjoint ⟨src, 800⟩ ⟨tbl, 768⟩
  oth_tbl : Region.Disjoint ⟨oth, 800⟩ ⟨tbl, 768⟩
  rc : ∀ r < 24, ∀ k < 4, s₀.mem.readW (VG.Proof.Sha3.X86_64.X4.la tbl r k) 64 = RC r

section
variable (src oth : Addr)

/-- The states the rounds read before round `r`, and those they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then src else oth
def nxt (r : Nat) : Addr := if r % 2 = 0 then oth else src

theorem cur_succ (r : Nat) : VG.Proof.Sha3.X86_64.X4.cur src oth (r + 1) = VG.Proof.Sha3.X86_64.X4.nxt src oth r := by
  simp only [VG.Proof.Sha3.X86_64.X4.cur, VG.Proof.Sha3.X86_64.X4.nxt]; split <;> split <;> first | rfl | omega

theorem nxt_succ (r : Nat) : VG.Proof.Sha3.X86_64.X4.nxt src oth (r + 1) = VG.Proof.Sha3.X86_64.X4.cur src oth r := by
  simp only [VG.Proof.Sha3.X86_64.X4.cur, VG.Proof.Sha3.X86_64.X4.nxt]; split <;> split <;> first | rfl | omega

theorem cur_cases (r : Nat) :
    (VG.Proof.Sha3.X86_64.X4.cur src oth r = src ∧ VG.Proof.Sha3.X86_64.X4.nxt src oth r = oth) ∨ (VG.Proof.Sha3.X86_64.X4.cur src oth r = oth ∧ VG.Proof.Sha3.X86_64.X4.nxt src oth r = src) := by
  simp only [VG.Proof.Sha3.X86_64.X4.cur, VG.Proof.Sha3.X86_64.X4.nxt]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

end

theorem in_append {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem la_rc (tbl : Addr) (r k : Nat) : VG.Proof.Sha3.X86_64.X4.la (tbl + BitVec.ofNat 64 (32 * r)) 0 k = VG.Proof.Sha3.X86_64.X4.la tbl r k := by
  simp only [VG.Proof.Sha3.X86_64.X4.la, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_zero, Nat.zero_add]

namespace Pre4
variable {s₀ : State} {src oth tbl : Addr} (h : VG.Proof.Sha3.X86_64.X4.Pre4 s₀ src oth tbl)
include h

theorem env (r : Nat) (hr : r < 24) :
    VG.Proof.Sha3.X86_64.X4.Env s₀.rd s₀.wr (VG.Proof.Sha3.X86_64.X4.cur src oth r) (VG.Proof.Sha3.X86_64.X4.nxt src oth r) (tbl + BitVec.ofNat 64 (32 * r)) := by
  have hsub : Region.Sub ⟨tbl + BitVec.ofNat 64 (32 * r), 32⟩ ⟨tbl, 768⟩ := Offset.sub_base tbl (by omega)
  rcases VG.Proof.Sha3.X86_64.X4.cur_cases src oth r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact ⟨fun i hi => VG.Proof.Sha3.X86_64.X4.in_append (h.src_in i hi), h.oth_in, h.tbl_in r hr, h.src_oth.symm,
      h.oth_tbl.sub_right hsub⟩
  · exact ⟨fun i hi => VG.Proof.Sha3.X86_64.X4.in_append (h.oth_in i hi), h.src_in, h.tbl_in r hr, h.src_oth,
      h.src_tbl.sub_right hsub⟩

/-- Writes to the states keep the table. -/
theorem rc_frame {m : Mem} (hf : Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem m) {r k : Nat} (hr : r < 24)
    (hk : k < 4) : m.readW (VG.Proof.Sha3.X86_64.X4.la tbl r k) 64 = RC r := by
  rw [hf.readW (Offset.contains_base tbl (show 32 * r + 8 * k + 64 / 8 ≤ 768 by omega) (by omega))
    (by simpa using ⟨h.src_tbl.symm, h.oth_tbl.symm⟩) (by decide)]
  exact h.rc r hr k hk

end Pre4

/-- The rounds' invariant, before round `r`. -/
structure LInv (s₀ : State) (src oth tbl : Addr) (A : Nat → VG.Proof.Sha3.X86_64.X4.KState) (r : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.Sha3.X86_64.X4.cur src oth r
  rsi : s.gpr .rsi = VG.Proof.Sha3.X86_64.X4.nxt src oth r
  rdx : s.gpr .rdx = tbl + BitVec.ofNat 64 (32 * r)
  rest : ∀ g, g ≠ .rax → g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → s.gpr g = s₀.gpr g
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : VG.Proof.Sha3.X86_64.X4.Lanes4 s.mem (VG.Proof.Sha3.X86_64.X4.cur src oth r) fun k => (List.range r).foldl rnd (A k)
  frame : Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem

theorem end_beq (tbl : Addr) (r : Nat) (hr : r < 24) :
    (tbl + BitVec.ofNat 64 (32 * r) + 32 - (tbl + BitVec.ofNat 64 768) == 0) = decide (r + 1 = 24) := by
  rw [show tbl + BitVec.ofNat 64 (32 * r) + 32 = tbl + BitVec.ofNat 64 (32 * r + 32) by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    Offset.add_sub_add_left, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  simp only [show (32 * r + 32 = 768) = (r + 1 = 24) by apply propext; omega]

theorem round_step {s₀ : State} {src oth tbl : Addr} {A : Nat → VG.Proof.Sha3.X86_64.X4.KState} (hp : VG.Proof.Sha3.X86_64.X4.Pre4 s₀ src oth tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {r : Nat} (hr : r < 24) {s : State}
    (hL : VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A r s) :
    WP isa (.block round) s fun s' =>
      eval .ne s' = some (!decide (r + 1 = 24)) ∧ VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A (r + 1) s' := by
  have he := hp.env r hr
  refine WP.mono (VG.Proof.Sha3.X86_64.X4.round_ok s _ _ _ _ (RC r) (by rw [hL.rd, hL.wr]; exact he) hL.rdi hL.rsi hL.rdx
    hL.state fun k hk => by rw [VG.Proof.Sha3.X86_64.X4.la_rc]; exact hp.rc_frame hL.frame hr hk)
    fun s' ⟨hl, hf, hrd, hwr, hdi, hsi, hdx, hg, hzf⟩ => ?_
  have hcx' : s.gpr .rcx = tbl + BitVec.ofNat 64 768 := by
    rw [hL.rest _ (by decide) (by decide) (by decide) (by decide), hcx]
  refine ⟨?_, by rw [hdi, VG.Proof.Sha3.X86_64.X4.cur_succ], by rw [hsi, VG.Proof.Sha3.X86_64.X4.nxt_succ],
    by rw [hdx, BitVec.add_assoc, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]; rfl,
    fun g a b c d => by rw [hg g a b c d, hL.rest g a b c d], hrd.trans hL.rd, hwr.trans hL.wr, ?_, ?_⟩
  · simp only [eval, hzf, hcx', Option.map_some, VG.Proof.Sha3.X86_64.X4.end_beq tbl r hr]
  · intro i hi k hk
    rw [VG.Proof.Sha3.X86_64.X4.cur_succ, hl i hi k hk]
    simp only [foldl_succ, ← outState_eq]
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_singleton] at hR; subst hR
    rcases VG.Proof.Sha3.X86_64.X4.cur_cases src oth r with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact ⟨_, by simp, fun _ h => h⟩

/-- Two rounds, from an even round `r`. -/
theorem body_ok {s₀ : State} {src oth tbl : Addr} {A : Nat → VG.Proof.Sha3.X86_64.X4.KState} (hp : VG.Proof.Sha3.X86_64.X4.Pre4 s₀ src oth tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {r : Nat} (hr : r + 2 ≤ 24) {s : State}
    (hL : VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A r s) :
    WP isa (.block (round ++ round)) s fun s' =>
      eval .ne s' = some (!decide (r + 2 = 24)) ∧ VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A (r + 2) s' := by
  rw [WP.block_append_iff]
  exact WP.mono (VG.Proof.Sha3.X86_64.X4.round_step hp hcx (by omega) hL) fun s₁ ⟨_, h₁⟩ => VG.Proof.Sha3.X86_64.X4.round_step hp hcx (by omega) h₁

/-- The 24 rounds: Keccak-f[1600] on each of the four states at `src`,
with `rdi`, `rsi` and every register but `rax` and `rdx` as they were. -/
theorem permute4_ok {s₀ : State} {src oth tbl : Addr} (hp : VG.Proof.Sha3.X86_64.X4.Pre4 s₀ src oth tbl)
    (hdi : s₀.gpr .rdi = src) (hsi : s₀.gpr .rsi = oth) (hdx : s₀.gpr .rdx = tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {A : Nat → VG.Proof.Sha3.X86_64.X4.KState} (hA : VG.Proof.Sha3.X86_64.X4.Lanes4 s₀.mem src A) :
    WP isa permute4 s₀ fun s =>
      VG.Proof.Sha3.X86_64.X4.Lanes4 s.mem src (fun k => keccakF (A k)) ∧ Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.gpr .rdx = tbl + BitVec.ofNat 64 768 ∧
      ∀ g, g ≠ .rax → g ≠ .rdx → s.gpr g = s₀.gpr g := by
  have h₀ : VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A 0 s₀ :=
    ⟨by rw [hdi]; rfl, by rw [hsi]; rfl, by rw [hdx]; exact (BitVec.add_zero _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl, by simpa [VG.Proof.Sha3.X86_64.X4.cur] using hA, Frame.refl _ _⟩
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A (2 * j) s
  refine WP.loop (M := isa) (Q := fun s => VG.Proof.Sha3.X86_64.X4.LInv s₀ src oth tbl A 24 s) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_)
    12 s₀ ⟨0, rfl, by omega, h₀⟩ |>.mono fun s hL => ?_
  · refine WP.mono (VG.Proof.Sha3.X86_64.X4.body_ok hp hcx (by omega) hL) fun s' ⟨he, hl⟩ => ?_
    by_cases hlast : 2 * j + 2 = 24
    · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
    · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 12 - (j + 1), by omega, j + 1, rfl, by omega,
        by rw [show 2 * (j + 1) = 2 * j + 2 by omega]; exact hl⟩
  · refine ⟨fun i hi k hk => ?_, hL.frame, hL.rd, hL.wr, hL.rdx, fun g a d => ?_⟩
    · have := hL.state i hi k hk
      simp only [VG.Proof.Sha3.X86_64.X4.cur, show 24 % 2 = 0 from rfl, ite_true] at this
      exact this
    · by_cases e₁ : g = .rdi
      · subst e₁; rw [hL.rdi, hdi]; rfl
      · by_cases e₂ : g = .rsi
        · subst e₂; rw [hL.rsi, hsi]; rfl
        · exact hL.rest g a e₁ e₂ d

end VG.Proof.Sha3.X86_64.X4

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.X4.Bytes`. -/
section

/-!
# Keccak-f[1600] four times at once on x86-64: the states byte by byte

Byte `q` of state `k` of the four interleaved at `p` is at `ba p k q` (byte `q
% 8` of lane `q / 8`); the lanes hold the states exactly when these bytes are
theirs (`lanes4_of_bytes`, `byte_of_lanes4`).
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64
open VG.Proof.Sha3 (byteOf byteOf_eq getElem!_eq)

/-- Byte `q` of state `k` of the four at `p`. -/
abbrev ba (p : Addr) (k q : Nat) : Addr := p + BitVec.ofNat 64 (32 * (q / 8) + 8 * k + q % 8)

/-- Two lanes with the same bytes. -/
theorem lane_ext {v w : BitVec 64} (h : ∀ j < 8, v.extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8) :
    v = w := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have := congrArg (·.getLsbD (b % 8)) (h (b / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (b / 8) + b % 8 = b by omega] at this

theorem la_byte (p : Addr) {i k j : Nat} (hj : j < 8) :
    VG.Proof.Sha3.X86_64.X4.la p i k + BitVec.ofNat 64 j = VG.Proof.Sha3.X86_64.X4.ba p k (8 * i + j) := by
  rw [VG.Proof.Sha3.X86_64.X4.la, BitVec.add_assoc, ← BitVec.ofNat_add, VG.Proof.Sha3.X86_64.X4.ba, show (8 * i + j) / 8 = i by omega,
    show (8 * i + j) % 8 = j by omega]

theorem lanes4_of_bytes {m : Mem} {p : Addr} {A : Nat → VG.Proof.Sha3.X86_64.X4.KState}
    (h : ∀ k < 4, ∀ q < 200, m (VG.Proof.Sha3.X86_64.X4.ba p k q) = byteOf (A k) q) : VG.Proof.Sha3.X86_64.X4.Lanes4 m p A := fun i hi k hk =>
  VG.Proof.Sha3.X86_64.X4.lane_ext fun j hj => by
    rw [byte_readW _ _ (by omega), VG.Proof.Sha3.X86_64.X4.la_byte _ hj, h k hk _ (by omega), byteOf_eq _ hi hj, VG.Proof.Sha3.getElem!_eq _ hi]

theorem byte_of_lanes4 {m : Mem} {p : Addr} {A : Nat → VG.Proof.Sha3.X86_64.X4.KState} (h : VG.Proof.Sha3.X86_64.X4.Lanes4 m p A) {k q : Nat} (hk : k < 4)
    (hq : q < 200) : m (VG.Proof.Sha3.X86_64.X4.ba p k q) = byteOf (A k) q := by
  rw [byteOf, ← h (q / 8) (by omega) k hk, byte_readW _ _ (by omega), VG.Proof.Sha3.X86_64.X4.la_byte _ (by omega),
    show 8 * (q / 8) + q % 8 = q by omega]

end VG.Proof.Sha3.X86_64.X4

end
