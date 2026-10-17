module

public import VerifiedGarbage.Proof.Rsa.Arm.CvEntry
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_crt_values` on ARMv7: the outputs, an invalid modulus, and the return

`Done s₀ s`: as `Base`, with the outputs written too. `fail_ok`: zeros to
the three outputs; `restore_ok`: the registers back.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

structure Done (s0 s : State) : Prop where
  pre : CvPre s0
  sp : s.sp = s0.sp
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : Frame [rS s0, rDp s0, rDq s0, rQi s0] s0.mem s.mem
  saved : ∀ i < 11, slot s.mem (cvB s0) (20 + 4 * i) = (s0.gpr (savedReg i)).toNat

theorem Base.done {s0 s : State} (h : Base s0 s) : Done s0 s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame.mono (by simp), h.saved⟩

theorem Done.arg {s0 s : State} (h : Done s0 s) {i : Nat} (hi : i < 12) : stackArg s i = stackArg s0 i := by
  have sp := h.pre.sp48
  unfold stackArg
  have ea : stackArgAddr s i = stackArgAddr s0 i := by simp only [stackArgAddr, h.sp]
  rw [ea]
  refine h.frame.readW (r := rA s0) ?_ (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega), addr_add (by omega), Nat.mul_zero, BitVec.add_zero, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.pre.sA.symm
    · exact h.pre.dpA.symm
    · exact h.pre.dqA.symm
    · exact h.pre.qiA.symm

theorem Done.rA_mem {s0 s : State} (h : Done s0 s) : rA s ∈ s.rd := by
  rw [h.rd, h.pre.rd]; simp [rA, stackArgAddr, h.sp]

theorem Done.of_rest {s0 s t : State} (h : Done s0 s) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) : Done s0 t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame, fun i hi => m ▸ h.saved i hi⟩

/-- The bytes of a region apart from a frame. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨a, n⟩) hd hn hi

/-- A slot of the header, apart from a frame. -/
theorem slot_frame {s0 : State} (h : CvPre s0) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (rS s0).Disjoint r) {i : Nat} (hi : i < 11) :
    slot m' (cvB s0) (20 + 4 * i) = slot m (cvB s0) (20 + 4 * i) := by
  have := h.fits
  have fS := h.fS
  have hz : 64 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega) this
  exact congrArg BitVec.toNat
    (hf.readW (r := rS s0) (Offset.contains_base _ (by simp only [cvZ] at hz; omega) (by omega)) hd (by decide))

/-- An output written. -/
theorem Done.out {s0 s t : State} (h : Done s0 s) {R : Region} (hR : R = rDp s0 ∨ R = rDq s0 ∨ R = rQi s0)
    (f : Frame [R] s.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Done s0 t := by
  have pre := h.pre
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans (f.mono ?_), fun i hi => ?_⟩
  · rcases hR with rfl | rfl | rfl <;> simp
  · rw [slot_frame pre f (fun r hr => ?_) hi, h.saved i hi]
    simp only [List.mem_singleton] at hr; subst hr
    rcases hR with rfl | rfl | rfl
    · exact pre.dpS.symm
    · exact pre.dqS.symm
    · exact pre.qiS.symm

theorem zero_mask_bytes (bs : List Byte) :
    bs.map (· &&& (0 : BitVec 32).setWidth 8) = List.replicate bs.length 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]; congr 1; simp

theorem bytesAt_length (m : Mem) (a : Addr) (n : Nat) : (Spec.Rsa.bytesAt m a n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-- `maskBytes` with `r2 = 0` on an output: zeros. -/
theorem zeroOut_ok {s0 s : State} (h : Done s0 s) {R : Region} (hR : R = rDp s0 ∨ R = rDq s0 ∨ R = rQi s0)
    {dst : BitVec 32} (hb : R.base = State.addr dst) (hn : 0 < R.len) (hl : R.len < 2 ^ 32)
    (fit : dst.toNat + R.len ≤ 2 ^ 32)
    (p0 : s.gpr .r0 = dst) (plr : s.gpr .lr = BitVec.ofNat 32 R.len) (p2 : s.gpr .r2 = 0) :
    WP isa maskBytes s fun t => Done s0 t ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) R.len = List.replicate R.len 0 ∧ Frame [R] s.mem t.mem ∧
      Rest [.r0, .r1, .lr] s t := by
  have hwr : R ∈ s.wr := by rw [h.wr, h.pre.wr]; rcases hR with rfl | rfl | rfl <;> simp
  have eR : R = ⟨State.addr dst, R.len⟩ := by cases R; simp_all
  refine WP.mono (maskBuffer_ok s hn hl fit ⟨R, hwr, by rw [← hb]; exact Region.contains_self _ _⟩
    p0 plr) fun t ⟨b, f, r⟩ => ⟨h.out hR (by rw [eR]; exact f) r.sp r.rd r.wr, ?_, by rw [eR]; exact f, r⟩
  rw [b, p2, zero_mask_bytes, bytesAt_length]

end VG.Proof.Rsa.Arm.CrtValues
