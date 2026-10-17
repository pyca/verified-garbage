module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFin
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_crt_values` on ARMv7: reading the numbers into arrays -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem val32_off (m : Mem) (base : Addr) (d : Nat) : ∀ (e n : Nat),
    val32 m (off base d) e n = val32 m base (d + e) n
  | _, 0 => rfl
  | e, n + 1 => by
    rw [val32, val32, val32_off m base d (e + 4) n, show d + (e + 4) = d + e + 4 by omega]
    simp only [w32, off, Offset.add_add]

theorem val32_zero_part {m : Mem} {base : Addr} {d K : Nat} (h : val32 m base d K = 0) {a c : Nat}
    (hac : a + c ≤ K) : val32 m base (d + 4 * a) c = 0 := by
  have e1 := val32_append m base d a (K - a)
  rw [show a + (K - a) = K by omega, h] at e1
  have p := Nat.two_pow_pos (32 * a)
  have z : val32 m base (d + 4 * a) (K - a) = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * a) (K - a)) with e | e
    · exact e
    · have : 0 < 2 ^ (32 * a) * val32 m base (d + 4 * a) (K - a) := Nat.mul_pos p e
      omega
  have e2 := val32_append m base (d + 4 * a) c (K - a - c)
  rw [show c + (K - a - c) = K - a by omega, z] at e2
  omega

theorem val32_low2 {m : Mem} {base : Addr} {d w : Nat} (h : val32 m base d (w + 2) < 2 ^ (32 * w)) :
    val32 m base d w = val32 m base d (w + 2) := by
  have h1 : val32 m base d (w + 1) = val32 m base d (w + 2) :=
    val32_low (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [← h1] at h ⊢
  exact val32_low h

theorem Keep.of_frame_arr {B : BitVec 32} {w j : Nat} {m m' : Mem}
    (h : Frame [⟨off (State.addr B) (arr w j), S w⟩] m m') (fit : arr w j + S w ≤ 2 ^ 64) :
    Keep B w [j] [] m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have := hx (arr w j, S w) (by simp [ranges])
  simp only [Region.Contains, off] at hc
  have := (Offset.lt_iff x (State.addr B) (d := arr w j) (n := S w) fit).mp (by omega)
  simp only [ofs] at *
  omega

/-- An input buffer: readable, apart from the working space, and short enough. -/
structure Input (s0 : State) (R : Region) (src : BitVec 32) (k : Nat) : Prop where
  base : R = ⟨State.addr src, k⟩
  rd : R ∈ s0.rd
  sep : R.Disjoint (rS s0)
  fit : src.toNat + k ≤ 2 ^ 32
  pos : 0 < k
  le : k ≤ cvK s0

/-- `load j`: array `j` := the `k` bytes at `r4` (`r6 = k`). -/
theorem load_ok {s0 s : State} (h : Base s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {j : Nat}
    (hj : j < nArr) {R : Region} {src : BitVec 32} {k : Nat} (hi : Input s0 R src k)
    (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (load j) s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      Keep (cvB s0) (cvW s0) [j] [] s.mem t.mem ∧
      val32 t.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (State.addr src) k) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have pre := h.pre
  have fit := hw.arr_fit hj
  have nw := hw.nowrap
  have w16 := pre.w16
  have kb := pre.kb
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  have hkw : k ≤ 4 * cvW s0 := by have := hi.le; simp only [cvW] at *; omega
  rw [load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  have rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  have mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have bu := h.of_rest rest mu
  have hu := hw.rest rest
  have ad : State.addr (cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)) = off (State.addr (cvB s0)) (arr (cvW s0) j) :=
    hw.addr (by omega)
  have p0 : u.gpr .r0 = cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)) (n := cvW s0 + 2)
    hi.pos (by omega) (by have := hi.fit; omega) hi.fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega)
    ⟨R, List.mem_append_left _ (by rw [bu.rd]; exact hi.rd), by rw [hi.base]; exact Region.contains_self _ _⟩
    ⟨rS s0, by rw [bu.wr, pre.wr]; simp, by rw [ad]; exact Offset.contains_base _ (by omega) (by omega)⟩
    (by rw [← hi.base, ad]
        refine fun a ha hb => hi.sep a ha ?_
        exact Region.Contains.byte (r := rS s0) (b := off (State.addr (cvB s0)) (arr (cvW s0) j)) (n := 4 * (cvW s0 + 2))
          (Offset.contains_base _ (by omega) (by omega)) (by simp only [Region.Contains] at hb; omega))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9,
          BitVec.ofNat_add]; rfl)
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  have k : Keep (cvB s0) (cvW s0) [j] [] u.mem t.mem := Keep.of_frame_arr f (by omega)
  refine ⟨bu.keep k (by simpa using hj) (by simp) (by simp) r.sp r.rd r.wr, hu.rest r, mu ▸ k, ?_,
    (rest.mono (by simp)).trans (r.mono (by simp))⟩
  rw [val32_off, Nat.add_zero] at v
  rw [v, mu, bytes_frame h.frame (by simpa [← hi.base] using hi.sep) (by omega)]

end VG.Proof.Rsa.Arm.CrtValues

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- A store outside the header's saved words keeps `Base`. -/
theorem Base.outside {s0 s t : State} (h : Base s0 s) {o n : Nat}
    (hf : Outside (State.addr (cvB s0)) o n s.mem t.mem) (ho : o + n ≤ 20 ∨ 64 ≤ o) (hn : o + n ≤ cvZ s0)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Base s0 t := by
  have fS := h.pre.fS
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans fun x hx => ?_, fun i hi => ?_⟩
  · exact hf x (.inr (Nat.le_trans hn (out_of_ofs (by simpa using hx))))
  · rw [← h.saved i hi]
    exact hf.w32 (d := 20 + 4 * i) (by omega) (by simp only [cvZ] at hn; omega)

abbrev pBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (cvPl s)
abbrev qBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6)) (cvQl s)
abbrev dBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8)) (cvDl s)

/-- The arrays the loads leave zero. -/
def zeroArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 19, 20, 21, 22, 23]

/-- After the loads. -/
structure StA (s0 s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  n : num s.mem (cvB s0) (cvW s0) aDQ = Spec.Rsa.os2ip (nBytes s0)
  p : num s.mem (cvB s0) (cvW s0) aP = Spec.Rsa.os2ip (pBytes s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = Spec.Rsa.os2ip (qBytes s0)
  d : num s.mem (cvB s0) (cvW s0) aD = Spec.Rsa.os2ip (dBytes s0)
  zeros : ∀ j ∈ zeroArrs, val32 s.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) = 0

end VG.Proof.Rsa.Arm.CrtValues
