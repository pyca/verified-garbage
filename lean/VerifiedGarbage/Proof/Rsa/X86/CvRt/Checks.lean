module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Eq
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Rsa.X86.InvGate
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Verified
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! ### `Rsa.X86.InvChoose`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.InvGuard`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.InvChoice`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.InvDispatch`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.CvInverseCall`, which this module and modules that import it used -/

section

/-! # The general inverse of CRT parameter calculation: a call of `vg_rsa_keygen_inverse`

`fallback_ok`: from the inverse's arrays (`InvInput`'s), `modulusAbove` makes the modulus more
than 1 where it was 1 (a `p` below 2, whose results the mask clears), and the call leaves the
gcd in array 1 and the inverse in array 3, as `KeyRt.inverse` does, by the callee's contract. The
call also writes the 52 bytes below `esp` (`Room`), which its frame (`OutsS`) lets change.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.Keys (Keep num slot ranges arr S invArrs invSlots)
open VG.Proof.RsaKeyGen.X86.KeyRuntime (OutsS)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero hdr seqs)
open VG.Impl.Rsa.X86.CrtValuesRt (lay sOne addLowTwice modulusAbove inverseArgs inverseCall fallback)
open VG.Impl.Rsa.X86.CrtValues (nArr)

variable {B : Addr} {Z len : Nat}

/-! ## Frames that let the call's stack change -/

theorem ranges_sub {w : Nat} {js ds js' ds' : List Nat} (hj : ∀ j ∈ js, j ∈ js' := by decide)
    (hd : ∀ d ∈ ds, d ∈ ds' := by decide) : ∀ r ∈ ranges w js ds, r ∈ ranges w js' ds' := by
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr ⊢
  rcases hr with ⟨j, hj', rfl⟩ | ⟨d, hd', rfl⟩
  · exact .inl ⟨j, hj j hj', rfl⟩
  · exact .inr ⟨d, hd d hd', rfl⟩

/-- A frame of the working space's ranges and the stack below `sp`, within the working space. -/
theorem outsS_ws {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} (h : OutsS B sp rs m m')
    (room : Room sp B Z) : Outs B (rs ++ [(Z, 2 ^ 64 - Z)]) m m' := by
  intro x hx
  apply h x (fun r hr => hx r (List.mem_append_left _ hr))
  intro hb
  obtain far := hx _ (List.mem_append_right _ (List.mem_singleton_self _))
  have := (x - B).isLt
  unfold ofs at far
  exact room.2.2 x (by simp only [Region.Contains]; omega_using [far]) hb

/-- An array of the working space outside the frame. -/
theorem outsS_num {sp : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : OutsS B sp (ranges w js ds) m m') (room : Room sp B Z) {j : Nat} (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (inside : arr w j + S w ≤ Z) (nowrap : Z ≤ 2 ^ 64) :
    num m' B w j = num m B w j := by
  obtain hS : 4 * w ≤ S w := by simp only [S]; omega_using []
  refine Outs.val32 (outsS_ws h room) (fun r hr => ?_) (by omega_using [inside, nowrap, hS])
  rcases List.mem_append.mp hr with hr | hr
  · simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
    · have := VG.Proof.Rsa.X86.Keys.arr_disj (w := w) (hj k hk); dsimp only; omega_using [hS, this]
    · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith
  · obtain rfl := List.mem_singleton.mp hr; dsimp only; omega_using [inside, hS]

/-- A word of an array of the working space outside the frame. -/
theorem outsS_word {sp : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : OutsS B sp (ranges w js ds) m m') (room : Room sp B Z) {j i : Nat} (hi : 4 * i + 4 ≤ S w)
    (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (inside : arr w j + S w ≤ Z) (nowrap : Z ≤ 2 ^ 64) :
    VG.Proof.Mont.w32 m' B (arr w j + 4 * i) = VG.Proof.Mont.w32 m B (arr w j + 4 * i) := by
  have := Outs.val32 (k := 1) (d := arr w j + 4 * i) (outsS_ws h room) (fun r hr => ?_) (by omega_using [hi, inside, nowrap])
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  rcases List.mem_append.mp hr with hr | hr
  · simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
    · have := VG.Proof.Rsa.X86.Keys.arr_disj (w := w) (hj k hk); dsimp only; omega_using [hi, this]
    · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith
  · obtain rfl := List.mem_singleton.mp hr; dsimp only; omega_using [hi, inside]

/-- A header word outside the frame. -/
theorem outsS_slot {sp : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : OutsS B sp (ranges w js ds) m m') (room : Room sp B Z) {e : Nat} (he : e + 4 ≤ hdr)
    (hZ : hdr ≤ Z) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) : slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) (outsS_ws h room) (fun r hr => ?_) (by simp only [hdr] at he; omega_using [he])
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  rcases List.mem_append.mp hr with hr | hr
  · simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
    · have : hdr ≤ arr w k := Nat.le_add_right _ _; dsimp only; omega_using [he, this]
    · exact hd d hd'
  · obtain rfl := List.mem_singleton.mp hr; dsimp only; omega_using [he, hZ]

/-! ## The modulus made more than 1 -/

/-- `[j]`'s low word plus twice the header word `sl`, for the word a bit, and `[j] = 1` where it
is one. -/
theorem addLowTwice_ok {s : State} {N : Nat} (h : RtWs lay s B Z len N) {j sl : Nat} (hj : j < N)
    (hsl : sl + 4 ≤ hdr) :
    WP isa (.block (addLowTwice j sl)) s fun t => RtWs lay t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      (slot s.mem B sl ≤ 1 → (slot s.mem B sl = 1 → num s.mem B (kw len) j = 1) →
        num t.mem B (kw len) j = num s.mem B (kw len) j + 2 * slot s.mem B sl) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have positive := h.kw_pos
  have head := h.ws.hdr_le
  unfold addLowTwice
  refine VG.Proof.Rsa.X86.KeyRt.lowPtr_ok h hj fun u hu K m p =>
    wp_movS (VG.Proof.Rsa.X86.KeyRt.lowSrc hu hj p) fun v V _ => ?_
  obtain hv := hu.keep V.keeps (by decide) (by decide) (by rw [V.mem]; exact Outside.refl _ _ _ _)
  refine wp_addS (readSrc_sc hv.ws.workspace (by unfold hdr at hsl head; omega_using [hsl, head])) fun x X _ => ?_
  obtain hx := hu.keep (V.keeps.trans X.keeps) (by decide) (by decide)
    (by rw [X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine wp_addS (readSrc_sc hx.ws.workspace (by unfold hdr at hsl head; omega_using [hsl, head])) fun y Y _ => ?_
  obtain KY : Keeps [.ecx] u y := V.keeps.trans (X.keeps.trans Y.keeps)
  obtain hy := hu.keep KY (by decide) (by decide) (by rw [Y.mem, X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeLow_ok hy hj (by rw [Rt.PtrAt, KY.1 _ (by decide)]; exact p))
    fun t ⟨ht, F, Vt, Kt, _⟩ => ?_
  obtain my : y.mem = s.mem := by rw [Y.mem, X.mem, V.mem, m]
  rw [my] at F Vt
  refine ⟨ht, F, ?_, ((K.mono (by decide)).trans (KY.mono (by decide))).trans (Kt.mono (by decide))⟩
  intro bit one
  obtain low := VG.Proof.Rsa.X86.KeyRt.low_word (B := B) (m := s.mem) (j := j) positive
  obtain sx : (x.mem.readW (off B sl) 32).toNat = slot s.mem B sl := by rw [X.mem, V.mem, m]
  obtain sv : (v.mem.readW (off B sl) 32).toNat = slot s.mem B sl := by rw [V.mem, m]
  rw [Vt, Y.gpr, X.gpr, V.gpr, m, BitVec.toNat_add, BitVec.toNat_add, sx, sv, ← low]
  rcases (show slot s.mem B sl = 0 ∨ slot s.mem B sl = 1 by omega_using [bit]) with e | e
  · rw [e]; omega_using []
  · rw [e, one e]

/-- What `modulusAbove` leaves: `m` (`[aM]`) 3 where it was 1, else as it was, in arrays 1 and
`aM`, and `2^(32 w) - m` in `aNM`. -/
theorem modulusAbove_ok {s : State} {N : Nat} (h : RtWs lay s B Z len N) (hN : 15 ≤ N)
    (odd : num s.mem B (kw len) aM % 2 = 1) (two : num s.mem B (kw len) 2 = 1)
    (zero : num s.mem B (kw len) aZero = 0) :
    WP isa (seqs modulusAbove) s fun t => RtWs lay t B Z len N ∧
      Keep B (kw len) [1, aM, aNM] [sOne] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      num t.mem B (kw len) aM = (if num s.mem B (kw len) aM = 1 then 3 else num s.mem B (kw len) aM) ∧
      num t.mem B (kw len) 1 = num t.mem B (kw len) aM ∧
      num t.mem B (kw len) aNM + num t.mem B (kw len) aM = 2 ^ (32 * kw len) := by
  obtain fit := fun j (hj : j < N) => h.ws.fit64 (j := j) hj
  unfold modulusAbove
  rw [VG.Proof.Rsa.X86.Keys.wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqSFast_ok h (d := sOne) (a := aM) (b := 2) (by unfold aM; omega_using [hN])
    (by omega_using [hN]) (by decide)) fun u ⟨hu, ku, fu, ru⟩ => ?_
  obtain mu : num u.mem B (kw len) aM = num s.mem B (kw len) aM :=
    ku.num (by decide) (by decide) (fit _ (by unfold aM; omega_using [hN]))
  rw [two] at fu
  rw [VG.Proof.Rsa.X86.Keys.wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addLowTwice_ok hu (j := aM) (sl := sOne) (by unfold aM; omega_using [hN]) (by decide))
    fun v ⟨hv, kv, ev, rv⟩ => ?_
  obtain ev' := ev (by rw [fu]; split <;> omega_using []) (by rw [fu]; split <;> simp_all)
  rw [mu, fu] at ev'
  obtain mv : num v.mem B (kw len) aM = (if num s.mem B (kw len) aM = 1 then 3 else num s.mem B (kw len) aM) := by
    rw [ev']; split <;> simp_all
  rw [VG.Proof.Rsa.X86.Keys.wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok hv (o := 1) (a := aM) (by omega_using [hN]) (by unfold aM; omega_using [hN])
    (by decide)) fun w ⟨hw, kw', ew, rw', _⟩ => ?_
  obtain mw : num w.mem B (kw len) aM = num v.mem B (kw len) aM :=
    kw'.num (by decide) (by decide) (fit _ (by unfold aM; omega_using [hN]))
  obtain zw : num w.mem B (kw len) aZero = 0 := by
    rw [kw'.num (by decide) (by decide) (fit _ (by unfold aZero; omega_using [hN])),
      kv.num (by decide) (by decide) (fit _ (by unfold aZero; omega_using [hN])),
      ku.num (by decide) (by decide) (fit _ (by unfold aZero; omega_using [hN])), zero]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok hw (o := aNM) (a := aZero) (b := aM) (by unfold aNM; omega_using [hN])
    (by unfold aZero; omega_using [hN]) (by unfold aM; omega_using [hN])) fun t ⟨ht, kt, et, bt, rt⟩ => ?_
  obtain mt : num t.mem B (kw len) aM = num w.mem B (kw len) aM :=
    kt.num (by decide) (by decide) (fit _ (by unfold aM; omega_using [hN]))
  obtain one : num t.mem B (kw len) 1 = num w.mem B (kw len) 1 :=
    kt.num (by decide) (by decide) (fit _ (by omega_using [hN]))
  obtain pos : 0 < num w.mem B (kw len) aM := by rw [mw, mv]; split <;> omega_arith
  refine ⟨ht, ?_, ((ru.mono (by decide)).trans ((rv.mono (by decide)).trans (rw'.mono (by decide)))).trans rt,
    by rw [mt, mw, mv], by rw [one, ew, mt, mw], ?_⟩
  · exact (ku.mono (by decide) (by decide)).trans ((kv.mono (by decide) (by decide)).trans
      ((kw'.mono (by decide) (by decide)).trans (kt.mono (by decide) (by decide))))
  · rw [mt]
    rw [zw, Nat.zero_add] at et
    have : (t.gpr .ebx).toNat = 1 := by
      rcases (show (t.gpr .ebx).toNat = 0 ∨ (t.gpr .ebx).toNat = 1 by omega_using [bt]) with e | e
      · rw [e, Nat.mul_zero] at et; omega
      · exact e
    rw [et, this, Nat.mul_one]

/-! ## The call -/

open VG.Proof.RsaKeyGen.X86.KeyRuntime (invArgs invEntry InvArguments invEntry_arg invEntry_frame
  invEntry_pre code_noSp code_stack rtWs_keepBelow)

/-- The words of working space the callee uses, for a length argument `a`. -/
abbrev invWords (a : Nat) : Nat := 35 + 15 * ((a + 7) / 8)

/-- What the callee writes lies in the inverse's arrays and header words. -/
theorem writes_ranges {a W i : Nat} (hka : kw a = W) (hw : Proof.RsaKeyGen.inverseWrites a i) :
    ¬ ∀ r ∈ ranges W invArrs invSlots, i < r.1 ∨ r.1 + r.2 ≤ i := by
  intro out
  simp only [kw, Spec.Rsa.modulusWords] at hka
  unfold Proof.RsaKeyGen.inverseWrites Proof.RsaKeyGen.inverseBytes at hw
  rcases hw with ⟨lo, hi⟩ | ⟨j, hj, lo, hi⟩
  · have h0 := out (VG.Impl.Rsa.X86.Keys.sOdd, 4) (by simp [ranges])
    obtain h1 := out (VG.Impl.Rsa.X86.Keys.sB, 4) (by simp [ranges])
    obtain h2 := out (VG.Impl.Rsa.X86.Keys.sC, 4) (by simp [ranges])
    simp only [VG.Impl.Rsa.X86.Keys.sOdd, VG.Impl.Rsa.X86.Keys.sB, VG.Impl.Rsa.X86.Keys.sC] at h0 h1 h2
    omega_using [lo, hi, h0, h1, h2]
  · have mem : j ∈ invArrs := by
      simp only [invArrs, VG.Impl.Rsa.X86.Keys.aT1, VG.Impl.Rsa.X86.Keys.aT2, VG.Impl.Rsa.X86.Keys.aT3,
        VG.Impl.Rsa.X86.Keys.aT4, List.mem_cons, List.not_mem_nil, or_false]
      omega_using [hj]
    obtain H := out (arr W j, S W) (List.mem_append_left _ (List.mem_map_of_mem mem))
    simp only [arr, S, hdr] at H
    obtain e : 8 * ((a + 7) / 8) + 8 = 4 * (W + 2) := by omega_using [hka]
    rw [e] at lo hi
    have := Nat.add_mul j 1 (4 * (W + 2))
    omega_using [lo, hi, H, this]

/-- What `vg_rsa_keygen_inverse`'s postcondition tells its caller. -/
theorem inversePost_of {s t : State} (post : VG.Proof.RsaKeyGen.X86.Inverse.contract.post s t) :
    (∀ i, i < VG.Proof.RsaKeyGen.X86.Inverse.size s →
      ¬ Proof.RsaKeyGen.inverseWrites (VG.Proof.RsaKeyGen.X86.Inverse.len s) i →
      t.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s + BitVec.ofNat 64 i) =
        s.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s + BitVec.ofNat 64 i)) ∧
    num t.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 1 =
      Nat.gcd (num s.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 0)
        (num s.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 8) ∧
    (num s.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 8 : Int) ∣
      (num t.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 3 : Int) *
          num s.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 0 -
        num t.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 1 ∧
    num t.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 3 <
      num s.mem (VG.Proof.RsaKeyGen.X86.Inverse.base s) (kw (VG.Proof.RsaKeyGen.X86.Inverse.len s)) 8 := by
  sig_post [VG.Proof.RsaKeyGen.X86.Inverse.contract, VG.Proof.RsaKeyGen.X86.Inverse.inverseStack,
    Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig, abi, argSlots, argVal, argBytes] at post
  simp only [← VG.Proof.RsaKeyGen.X86.Inverse.inverseNum_num]
  exact post

/-- What the call needs of the state it is made from. -/
structure CallAt (B : Addr) (Z len : Nat) (a : Nat) (u : State) : Prop where
  ws : RtWs lay u B Z len nArr
  room : Room (u.gpr .esp) B Z
  lenLe : a ≤ 1024
  words : kw a = kw len
  eax : u.gpr .eax = BitVec.ofNat 32 a
  ecx : u.gpr .ecx = BitVec.ofNat 32 (invWords a)
  odd : num u.mem B (kw len) aM % 2 = 1
  large : 1 < num u.mem B (kw len) aM
  v : num u.mem B (kw len) 1 = num u.mem B (kw len) aM
  x₁ : num u.mem B (kw len) 2 = 1
  x₂ : num u.mem B (kw len) 3 = 0
  negated : num u.mem B (kw len) aNM + num u.mem B (kw len) aM = 2 ^ (32 * kw len)
  zero : num u.mem B (kw len) aZero = 0

namespace CallAt
variable {a : Nat} {u : State}

theorem fits (C : CallAt B Z len a u) : arr (kw a) 15 ≤ Z := by
  have := C.ws.ws.fits
  rw [C.words]
  simp only [arr, S, nArr] at this ⊢
  omega_using [this]

theorem size (C : CallAt B Z len a u) : 8 * invWords a ≤ Z := by
  have fits := C.fits
  simp only [arr, S, hdr, kw, Spec.Rsa.modulusWords] at fits
  unfold invWords
  omega_using [fits]

theorem ptrBound (C : CallAt B Z len a u) : B.toNat < 2 ^ 32 := by
  have := C.fits
  have := C.ws.ws.workspace.nowrap
  simp only [arr, hdr] at *
  omega_arith

theorem lenLow (C : CallAt B Z len a u) : 1 ≤ a := by
  obtain wpos : 0 < kw a := by rw [C.words]; exact C.ws.kw_pos
  by_contra c
  rw [show a = 0 by omega] at wpos
  exact absurd wpos (by decide)

theorem args (C : CallAt B Z len a u) : InvArguments B a (invWords a) u := by
  refine ⟨?_, C.ecx, C.eax⟩
  apply BitVec.eq_of_toNat_eq
  rw [C.ws.edi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt C.ptrBound]

theorem entry_eq (B : Addr) (a : Nat) (u : State) :
    (pushed invArgs u).callEntry.withRegions [⟨(below (u.gpr .esp) 12).base, 12⟩] [⟨B, 8 * invWords a⟩] =
      invEntry B (8 * invWords a) u := by
  unfold invEntry
  rw [callEntry_argAddr0]
  rfl

theorem callPre (C : CallAt B Z len a u) :
    CallPre VG.Proof.RsaKeyGen.X86.Inverse.contract invArgs [⟨(below (u.gpr .esp) 12).base, 12⟩]
      [⟨B, 8 * invWords a⟩] u := by
  have nowrap := C.ws.ws.workspace.nowrap
  obtain pre := invEntry_pre C.args nowrap C.lenLow C.lenLe rfl C.fits C.room.1 C.room.2.2
    (by rw [C.words]; exact C.odd) (by rw [C.words]; exact C.large) (by rw [C.words]; exact C.v)
    (by rw [C.words]; exact C.x₁) (by rw [C.words]; exact C.x₂) (by rw [C.words]; exact C.negated)
    (by rw [C.words]; exact C.zero)
  have size := C.size
  obtain wsIn : InRegions u.wr B (8 * invWords a) :=
    ⟨_, C.ws.ws.workspace.wr, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [size]⟩
  refine ⟨by rw [entry_eq B a u]; exact pre, ?_, ?_⟩
  · apply Covers.append_left
    · apply Covers.of_mem
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact List.mem_append_right _ List.mem_cons_self
    · exact Covers.one (by
        obtain ⟨r, hr, hc⟩ := wsIn
        exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), hc⟩)
  · exact Covers.one (by
      obtain ⟨r, hr, hc⟩ := wsIn
      exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩)

end CallAt

/-- The call: the gcd in array 1 and the inverse in array 3, by the callee's contract, the rest of
the working space but the inverse's arrays and header words as it was, and the stack below `esp`
the only other memory written. -/
theorem call_ok {a : Nat} {u : State} (C : CallAt B Z len a u) :
    WP isa inverseCall u fun t =>
      RtWs lay t B Z len nArr ∧
      OutsS B (u.gpr .esp) (ranges (kw len) invArrs invSlots) u.mem t.mem ∧
      num t.mem B (kw len) 1 = Nat.gcd (num u.mem B (kw len) 0) (num u.mem B (kw len) aM) ∧
      (num u.mem B (kw len) aM : Int) ∣
        (num t.mem B (kw len) 3 : Int) * num u.mem B (kw len) 0 - num t.mem B (kw len) 1 ∧
      num t.mem B (kw len) 3 < num u.mem B (kw len) aM ∧
      Keeps [.eax, .ecx, .edx] u t := by
  have h := C.ws
  have nowrap := h.ws.workspace.nowrap
  have far := C.room.2.2
  have lowSp : 52 ≤ (u.gpr .esp).toNat := C.room.1
  have hka := C.words
  have ptrBound := C.ptrBound
  have size := C.size
  have A := C.args
  refine WP.callWith VG.Proof.RsaKeyGen.X86.Inverse.verified.1 code_noSp (by decide : invArgs ≠ [])
    (by decide : Reg.esp ∉ invArgs) (by rw [code_stack]; change 32 ≤ _; omega_using [lowSp]) C.callPre ?_
  intro t rdT wrT saved frame post
  obtain ⟨e₂, mem₂, post⟩ := post
  rw [CallAt.entry_eq B a u] at post
  obtain ⟨inside, gcd, bezout, lt⟩ := inversePost_of post
  obtain fit16 : 16 ≤ (u.gpr .esp).toNat := by omega_using [lowSp]
  obtain wordsBound : invWords a < 2 ^ 32 := by have := C.lenLe; omega_using [nowrap, size]
  obtain arg0 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 0) (by decide)
  obtain arg1 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 1) (by decide)
  obtain arg2 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 2) (by decide)
  simp only [↓reduceIte, Nat.reduceEqDiff] at arg0 arg1 arg2
  obtain baseE : VG.Proof.RsaKeyGen.X86.Inverse.base (invEntry B (8 * invWords a) u) = B := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.base
    rw [arg0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt B.isLt
  obtain sizeE : VG.Proof.RsaKeyGen.X86.Inverse.size (invEntry B (8 * invWords a) u) = 8 * invWords a := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.size
    rw [arg1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordsBound]
  obtain lenE : VG.Proof.RsaKeyGen.X86.Inverse.len (invEntry B (8 * invWords a) u) = a := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.len
    rw [arg2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := C.lenLe; omega_using [this])]
  simp only [baseE, sizeE, lenE, hka] at inside gcd bezout lt
  obtain FE := invEntry_frame (B := B) (L := 8 * invWords a) fit16
  obtain farU : (⟨B, Z⟩ : Region).Disjoint (below (u.gpr .esp) 16) :=
    far.sub_right (below_sub (by decide) lowSp)
  have entryNum {j : Nat} (hj : j < 15) :
      num (invEntry B (8 * invWords a) u).mem B (kw len) j = num u.mem B (kw len) j :=
    VG.Proof.RsaKeyGen.X86.KeyRuntime.frame_num FE farU nowrap
      (Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end hj) (by have := C.fits; rwa [hka] at this))
  rw [entryNum (j := 0) (by decide), entryNum (j := 8) (by decide)] at gcd bezout
  rw [entryNum (j := 8) (by decide)] at lt
  obtain mem₂ : Frame [below (u.gpr .esp) 16] e₂.mem t.mem :=
    Frame.below_mono (wr := []) mem₂ (by decide) fit16
  have backNum {j : Nat} (hj : j < 15) : num t.mem B (kw len) j = num e₂.mem B (kw len) j :=
    VG.Proof.RsaKeyGen.X86.KeyRuntime.frame_num mem₂ farU nowrap
      (Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end hj) (by have := C.fits; rwa [hka] at this))
  rw [← backNum (j := 1) (by decide)] at gcd bezout
  rw [← backNum (j := 3) (by decide)] at bezout lt
  obtain Kt : Keeps [.eax, .ecx, .edx] u t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp [calleeSaved] at hr ⊢
  obtain stackFrame : Frame [⟨B, Z⟩, below (u.gpr .esp) 52] u.mem t.mem := by
    refine frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix size⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [code_stack]
      exact below_sub (by decide) lowSp
  refine ⟨rtWs_keepBelow h Kt (by decide) (by decide) stackFrame lowSp
    (by have := C.room.2.1; change _ + 8 + 4 * 7 ≤ _; omega_using [this])
    (by have := C.room.2.1; change _ + 8 + 4 * 14 ≤ _; omega_using [this]), ?_, gcd, bezout, lt, Kt⟩
  intro x hx hz
  by_cases hin : (⟨B, 8 * invWords a⟩ : Region).Contains x 1
  · have hi : ofs B x < 8 * invWords a := by
      simp only [Region.Contains] at hin
      unfold ofs
      omega_using [hin]
    obtain changed := inside (ofs B x) hi fun c => writes_ranges hka c hx
    obtain back : B + BitVec.ofNat 64 (ofs B x) = x := by
      unfold ofs
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
      exact BitVec.sub_add_cancel x B
    rw [back] at changed
    rw [mem₂ x (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact farU x (Region.sub_prefix size x hin)), changed]
    apply FE x
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact farU x (Region.sub_prefix size x hin)
  · apply frame x
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hin
    · intro c
      apply hz
      rw [code_stack] at c
      exact below_sub (by decide) lowSp x c

/-- Two calls from states with the same length argument and `esp` give the callee the same public
data. -/
theorem CallAt.pub {a : Nat} {u₁ u₂ : State} (C₁ : CallAt B Z len a u₁) (C₂ : CallAt B Z len a u₂)
    (sp : u₁.gpr .esp = u₂.gpr .esp) :
    VG.Proof.RsaKeyGen.X86.Inverse.contract.pub (invEntry B (8 * invWords a) u₁)
      (invEntry B (8 * invWords a) u₂) := by
  obtain fit₁ : 16 ≤ (u₁.gpr .esp).toNat := by have := C₁.room.1; omega_using [this]
  obtain fit₂ : 16 ≤ (u₂.gpr .esp).toNat := by have := C₂.room.1; omega_using [this]
  obtain sa := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * invWords a) C₁.args fit₁ hi
  obtain ta := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * invWords a) C₂.args fit₂ hi
  obtain esp : (invEntry B (8 * invWords a) u₁).gpr .esp = (invEntry B (8 * invWords a) u₂).gpr .esp := by
    change (pushed invArgs u₁).callEntry.gpr .esp = (pushed invArgs u₂).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', sp]
  sig_pub [VG.Proof.RsaKeyGen.X86.Inverse.contract, VG.Proof.RsaKeyGen.X86.Inverse.inverseStack,
    Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 3), sa (by decide : 1 < 3), sa (by decide : 2 < 3),
    ta (by decide : 0 < 3), ta (by decide : 1 < 3), ta (by decide : 2 < 3), ↓reduceIte]
  exact ⟨esp, trivial, trivial, trivial⟩

/-- The call's trace depends only on its public data: the working space's address, the length and
`esp`. -/
theorem call_trace (B : Addr) (Z len a : Nat) (sp : BitVec 32) :
    RelCT isa (fun u₁ u₂ => (CallAt B Z len a u₁ ∧ u₁.gpr .esp = sp) ∧ CallAt B Z len a u₂ ∧ u₂.gpr .esp = sp)
      inverseCall fun _ _ => True := by
  refine VG.X86.RelCT.callWith (rs := invArgs) VG.Proof.RsaKeyGen.X86.Inverse.verified.1
    VG.Proof.RsaKeyGen.X86.Inverse.verified.2.1 [⟨(below sp 12).base, 12⟩] [⟨B, 8 * invWords a⟩] ?_
  intro u₁ u₂ ⟨⟨C₁, s₁⟩, C₂, s₂⟩
  have p₁ := C₁.callPre
  have p₂ := C₂.callPre
  rw [s₁] at p₁
  rw [s₂] at p₂
  refine ⟨p₁, p₂, s₁.trans s₂.symm, ?_⟩
  obtain e₁ := CallAt.entry_eq B a u₁
  obtain e₂ := CallAt.entry_eq B a u₂
  rw [s₁] at e₁
  rw [s₂] at e₂
  rw [e₁, e₂]
  exact C₁.pub C₂ (s₁.trans s₂.symm)

end VG.Proof.Rsa.X86.CrtValuesRt

end

end

/-! # Public-length selection of the verified batched inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
 VG.Proof.Weierstrass VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)
open VG.Impl.Rsa.X86.CrtValuesRt (lay)
open VG.Impl.Rsa.X86.CrtValues (nArr)
open VG.Proof.Weierstrass.X86.Inv (wordClob)

 def inverseM (P : Nat) := 2*(P/2)+1
 structure InvInput (args : Nat → BitVec 32) (base : Addr) (size len P Q : Nat) (s : State) : Prop where
  ws : RtWs lay s base size len nArr
  gate : InvGate args base size P Q s
  u : num s.mem base (kw len) 0=Q
  m : num s.mem base (kw len) aM=inverseM P
  nm : num s.mem base (kw len) aNM+inverseM P=2^(32*kw len)
  zero : num s.mem base (kw len) aZero=0
  bank : bank s.mem base (kw len) 0=(Q,inverseM P,1,0)

 /-- The arrays the inverse may change: its own, and the modulus `m` and `2^(32 w) - m`, which the
 general inverse sets to 3 and `2^(32 w) - 3` where `m` is 1. -/
 abbrev invOut : List Nat := invArrs ++ [aM, aNM]

 /-- What the inverse leaves: its frame lets the stack below `esp` that the general inverse's call
 uses change too. -/
 def InvPost (base : Addr) (size len P Q : Nat) (s t : State) : Prop :=
  RtWs lay t base size len nArr ∧
  VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS base (s.gpr .esp) (ranges (kw len) invOut (invSlots ++ rtSlots))
    s.mem t.mem ∧
  Keeps wordClob s t ∧
  (1<inverseM P → num t.mem base (kw len) 1=Nat.gcd Q (inverseM P) ∧
   (inverseM P : Int)∣(num t.mem base (kw len) 3 : Int)*Q-num t.mem base (kw len) 1 ∧
   num t.mem base (kw len) 3<inverseM P)

 theorem InvInput.rest {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s t : State} {regs : List Reg}
    (h : InvInput args base size len P Q s) (K : Keeps regs s t) (di : .edi∉regs) (sp : .esp∉regs)
    (mem : t.mem=s.mem) : InvInput args base size len P Q t := by
  have O : Outside base 0 size s.mem t.mem := by rw [mem]; exact Outside.refl _ _ _ _
  exact ⟨h.ws.keep K di sp O,h.gate.keep K sp O,mem ▸ h.u,mem ▸ h.m,mem ▸ h.nm,mem ▸ h.zero,mem ▸ h.bank⟩

 /-- What the call's setup leaves: the call's input, with the modulus 3 where it was 1. -/
 theorem callSetup_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.CrtValuesRt.callSetup s fun v =>
      CallAt base size len (args 7).toNat v ∧ v.gpr .esp = s.gpr .esp ∧
      Keep base (kw len) [1, aM, aNM] [VG.Impl.Rsa.X86.CrtValuesRt.sOne] s.mem v.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s v ∧
      num v.mem base (kw len) aM = (if inverseM P = 1 then 3 else inverseM P) ∧
      num v.mem base (kw len) 0 = Q := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  have b := h.bank
  simp only [bank, Prod.mk.injEq] at b
  obtain ⟨b0, -, b2, b3⟩ := b
  have odd : num s.mem base (kw len) aM % 2 = 1 := by rw [h.m]; unfold inverseM; omega
  unfold VG.Impl.Rsa.X86.CrtValuesRt.callSetup
  refine WP.seq (WP.mono (modulusAbove_ok h.ws (by decide) odd b2 h.zero) fun u ⟨hu, ku, ru, mu, vu, nu⟩ => ?_)
  obtain ⟨a, ha, hka, LA⟩ := hu.lenArg
  change kw a = kw len at hka
  have ga : a = (args 7).toNat := by
    have nArg := h.gate.nArg.keep ru (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws ku (by decide) (by decide))
    have eq : BitVec.ofNat 32 a = args 7 := Option.some.inj (LA.readSrc.symm.trans nArg.readSrc)
    have ae := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ae
    exact ae
  subst ga
  unfold VG.Impl.Rsa.X86.CrtValuesRt.inverseArgs
  refine VG.Proof.RsaKeyGen.X86.KeyRuntime.callSetup_ok (L := lay) LA.readSrc ha fun v Kv mv eax ecx => ?_
  have hv : RtWs lay v base size len nArr :=
    hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  have espV : v.gpr .esp = s.gpr .esp := (Kv.1 .esp (by decide)).trans (ru.1 .esp (by decide))
  have kept {j : Nat} (hj : j < nArr) (out : j ∉ [1, aM, aNM]) :
      num v.mem base (kw len) j = num s.mem base (kw len) j := by
    rw [mv]
    exact ku.num (fun k hk e => out (e ▸ hk)) (by decide) (fit j hj)
  have mV : num v.mem base (kw len) aM = (if inverseM P = 1 then 3 else inverseM P) := by rw [mv, mu, h.m]
  refine ⟨⟨hv, espV ▸ h.gate.room, ha, hka, eax, ecx, ?_, ?_, by rw [mv]; exact vu,
      by rw [kept (by decide) (by decide), b2], by rw [kept (by decide) (by decide), b3], by rw [mv]; exact nu,
      by rw [kept (by decide) (by decide), h.zero]⟩, espV, mv ▸ ku, ru.trans (Kv.mono (by decide)), mV,
    by rw [kept (by decide) (by decide), b0]⟩
  · rw [mV]; unfold inverseM; split <;> omega
  · rw [mV]; unfold inverseM; split <;> omega

 theorem inverseFallback_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.CrtValuesRt.fallback s (InvPost base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.CrtValuesRt.fallback
  refine WP.seq (WP.mono (callSetup_ok h) fun v ⟨C, espV, kv, rv, mV, qV⟩ => ?_)
  refine WP.mono (call_ok C) fun t ⟨ht, O, G, Bz, Lt, Kt⟩ => ?_
  rw [espV] at O
  refine ⟨ht, ?_, (rv.mono (by decide)).trans (Kt.mono (by decide)), ?_⟩
  · exact (VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs kv).mono (ranges_sub (by decide) (by decide)) |>.trans
      (O.mono (ranges_sub (by decide) (by decide)))
  · intro large
    have mM : num v.mem base (kw len) aM = inverseM P := by rw [mV, ite_eq_right_iff.mpr (by omega)]
    rw [mM, qV] at G Bz
    rw [mM] at Lt
    exact ⟨G, Bz, Lt⟩

 /-- The body's writes are within the inverse's arrays and the header words from 16 on. -/
 theorem body_keep {base : Addr} {len : Nat} {m m' : Mem} (hpos : 0 < kw len)
    (U : Unch base (VG.Proof.Rsa.X86.InvBatchRt.bodyWrites len) m m') :
    Keep base (kw len) invArrs (invSlots ++ rtSlots) m m' := by
  intro x hx
  apply U x
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq len
  have harr : ∀ j ∈ invArrs, ofs base x < arr (kw len) j ∨ arr (kw len) j + S (kw len) ≤ ofs base x :=
    fun j hj => hx _ (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨j, hj, rfl⟩)
  have hsl : ∀ d ∈ invSlots ++ rtSlots, ofs base x < d ∨ d + 4 ≤ ofs base x :=
    fun d hd => hx _ (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, List.mem_append.mp hd, rfl⟩)
  have hS : S (kw len) = 8 * VG.Proof.Rsa.X86.InvBatchRt.nw len + 8 := by
    show 4 * (kw len + 2) = _; omega
  have ra (j : Nat) : VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a j) =
      arr (kw len) j := by
    show VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) j + 0 * (4 * (kw len / 2)) + 0 = _
    rw [VG.Proof.Rsa.X86.InvBatchRt.offset_eq]; simp
  -- A byte in one of the ranges is in a word or an array of the frame.
  have words : ∀ k < 22, 16 + 4 * k ∈ invSlots ++ rtSlots := by decide
  have arrs0 : ∀ j < 8, j ∈ invArrs := by decide
  have arrs11 : ∀ j < 4, 11 + j ∈ invArrs := by decide
  have inArr (lo j₀ c : Nat) (hc : ∀ j < c, j₀ + j ∈ invArrs) (hlo : lo = arr (kw len) j₀)
      (h₁ : lo ≤ ofs base x) (h₂ : ofs base x < lo + c * S (kw len)) : False := by
    have Spos : 0 < S (kw len) := by omega
    obtain ⟨j, hj⟩ : ∃ j, j = (ofs base x - lo) / S (kw len) := ⟨_, rfl⟩
    have hq := Nat.div_add_mod (ofs base x - lo) (S (kw len))
    have hr := Nat.mod_lt (ofs base x - lo) Spos
    rw [← hj] at hq
    have hcS := Nat.mul_comm c (S (kw len))
    have hjc : j < c := by
      apply Nat.lt_of_mul_lt_mul_left (a := S (kw len))
      omega
    have e : arr (kw len) (j₀ + j) = lo + S (kw len) * j := by
      rw [hlo]; simp only [arr, Nat.add_mul]; rw [Nat.mul_comm j]; omega
    have := harr (j₀ + j) (hc j hjc)
    rw [e] at this
    omega
  intro w hw
  simp only [VG.Proof.Rsa.X86.InvBatchRt.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
  have e16 : VG.Impl.Rsa.X86.InvBatchRt.win = 16 := rfl
  rcases hw with rfl | rfl | rfl
  · change ofs base x < VG.Impl.Rsa.X86.InvBatchRt.win ∨ VG.Impl.Rsa.X86.InvBatchRt.win + 88 ≤ ofs base x
    by_contra hc
    have := hsl (16 + 4 * ((ofs base x - 16) / 4)) (words _ (by omega))
    omega
  · change ofs base x < _ ∨ _ + _ ≤ ofs base x
    by_contra hc
    rw [ra, ← hS] at hc
    exact inArr _ 0 8 (fun j hj => by simpa using arrs0 j hj) rfl (by omega) (by omega)
  · change ofs base x < _ ∨ _ + _ ≤ ofs base x
    by_contra hc
    rw [ra, ← hS] at hc
    exact inArr _ 11 4 (fun j hj => arrs11 j hj) rfl (by omega) (by omega)

 theorem inverseBodyRt_ok [VG.Proof.Rsa.X86.BatchLaw] {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) (hn2 : 2 ≤ VG.Proof.Rsa.X86.InvBatchRt.nw len)
    (he : VG.Proof.Rsa.X86.InvBatchRt.nw len % 2 = 0)
    (pb : (args 9).toNat ≤ 4 * VG.Proof.Rsa.X86.InvBatchRt.nw len)
    (qb : (args 11).toNat ≤ 4 * VG.Proof.Rsa.X86.InvBatchRt.nw len) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.body lay) s (InvPost base size len P Q s) := by
  have hs := h.ws.ws.workspace
  have nw := hs.nowrap
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq len
  let n := VG.Proof.Rsa.X86.InvBatchRt.nw len
  have ra (j : Nat) : VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a j) =
      arr (kw len) j := by
    show VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) j + 0 * (4 * (kw len / 2)) + 0 = _
    rw [VG.Proof.Rsa.X86.InvBatchRt.offset_eq]; simp
  have pc : inverseM P < 2 ^ (32 * n) := odd_modulus_bound (by omega) (prime_bound h.gate.pBound pb)
  have qc : Q < 2 ^ (32 * n) := prime_bound h.gate.qBound qb
  have mv : val32 s.mem base (VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 8)) n =
      inverseM P := by
    rw [ra]
    change val32 s.mem base (arr (kw len) aM) n = inverseM P
    have v : val32 s.mem base (arr (kw len) aM) (kw len) = inverseM P := h.m
    rw [prefix_eq (w := kw len) (by omega) (by rw [v]; exact pc), v]
  have qv : val32 s.mem base (VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 0)) n = Q := by
    rw [ra]
    have v : val32 s.mem base (arr (kw len) 0) (kw len) = Q := h.u
    rw [prefix_eq (w := kw len) (by omega) (by rw [v]; exact qc), v]
  refine WP.mono (VG.Proof.Rsa.X86.BatchLaw.inv_ok h.ws (by decide) hn2 he mv qv (by unfold inverseM; omega))
    fun t ⟨_, G, A, small, R, O⟩ => ?_
  have bankKeep := body_keep h.ws.ws.wpos O
  have outside := keep_outside h.ws.ws bankKeep (by decide) (by decide)
  refine ⟨h.ws.keep R (by decide) (by decide) outside,
    VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs (bankKeep.mono (by decide) (by decide)), R, ?_⟩
  intro large
  have vm : VG.Proof.Rsa.X86.InvBatchRt.virtualMod (inverseM P) = inverseM P := by
    unfold VG.Proof.Rsa.X86.InvBatchRt.virtualMod; rw [ite_eq_right (by omega)]
  simp only [vm, ra] at G A small
  change num t.mem base (kw len) 1 = Nat.gcd (inverseM P) Q at G
  change (inverseM P : Int) ∣ (num t.mem base (kw len) 3 : Int) * Q - (Nat.gcd (inverseM P) Q : Int) at A
  change num t.mem base (kw len) 3 < inverseM P at small
  refine ⟨G.trans (Nat.gcd_comm _ _), ?_, small⟩
  rw [G]; exact A

end VG.Proof.Rsa.X86.CrtValuesRt

end

end

/-! # Comparing public lengths without changing the inverse inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
 VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.KeyRt VG.Impl.Rsa.X86.KeyRt

 theorem cmpBoth {s : State} {d : Reg} {src : Src} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (h : readSrc s src=some v)
    (k : ∀ t,Fupd s t → t.zf=some (s.gpr d-v==0) →
      t.cf=some (decide ((s.gpr d).toNat<v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src::is)) s Q :=
  cons (s':=arithFlags s (s.gpr d-v) (decide ((s.gpr d).toNat<v.toNat)) (subOverflow (s.gpr d) v (s.gpr d-v)))
    (by simp only [exec,execAlu,h,Option.bind_some])
    (k _ ⟨rfl,rfl,rfl,rfl,rfl⟩ rfl rfl)

 theorem invCompare_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q i limit : Nat} {s : State} {v : BitVec 32}
    (h : InvInput args base size len P Q s) (arg : CallArgument s base size i v) (small : limit<2^32) :
    WP isa (.block [.mov .eax (.mem (argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]) s fun t =>
      InvInput args base size len P Q t ∧ Keeps [.eax] s t ∧ t.mem=s.mem ∧
      t.zf=some (decide (v=BitVec.ofNat 32 limit)) ∧ t.cf=some (decide (v.toNat<limit)) := by
  refine wp_movS arg.readSrc fun u U _ => cmpBoth rfl fun t T zf cf => WP.block_nil ?_
  have K := U.keeps.trans (T.keeps _)
  have mem : t.mem=s.mem := T.mem.trans U.mem
  refine ⟨h.rest K (by decide) (by decide) mem,K,mem,?_,?_⟩
  · rw [zf,U.gpr]
    congr 1
    rw [Bool.eq_iff_iff,beq_iff_eq,decide_eq_true_iff,BitVec.sub_eq_iff_eq_add]
    change v=0#32+BitVec.ofNat 32 limit ↔ _
    rw [BitVec.zero_add]
  · rw [cf,U.gpr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

 theorem InvPost.pre_rest {base : Addr} {size len P Q : Nat} {s u t : State} {regs : List Reg}
    (h : InvPost base size len P Q u t) (K : Keeps regs s u)
    (incl : ∀ r∈regs,r∈VG.Proof.Weierstrass.X86.Inv.wordClob) (mem : u.mem=s.mem) :
    InvPost base size len P Q s t := by
  have sp : u.gpr .esp=s.gpr .esp := K.1 .esp fun e => by
    have := incl _ e; simp [VG.Proof.Weierstrass.X86.Inv.wordClob] at this
  exact ⟨h.1,mem ▸ sp ▸ h.2.1,(K.mono incl).trans h.2.2.1,h.2.2.2⟩

end VG.Proof.Rsa.X86.CrtValuesRt

end

end

/-! # The public guard of the batched inverse

`guard_ok`: CF set exactly for the lengths the batches take (`Eligible`), the inputs kept.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.KeyRt

/-- `n_len` a multiple of 16 and at least 128, and the primes' lengths at most `n_len / 2`. -/
def Eligible (args : Nat → BitVec 32) : Prop :=
  (args 7).toNat % 16 = 0 ∧ 128 ≤ (args 7).toNat ∧ (args 9).toNat < (args 7).toNat / 2 + 1 ∧
    (args 11).toNat < (args 7).toNat / 2 + 1

instance (args : Nat → BitVec 32) : Decidable (Eligible args) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure Guarded (args : Nat → BitVec 32) (base : Addr) (size len P Q : Nat) (s t : State) : Prop where
  input : InvInput args base size len P Q t
  keeps : Keeps [.eax, .ecx] s t
  mem : t.mem = s.mem
  cf : t.cf = some (decide (Eligible args))

theorem reject_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.InvBatchRt.reject s fun t =>
      InvInput args base size len P Q t ∧ Keeps [.eax] s t ∧ t.mem = s.mem ∧ t.cf = some false := by
  refine cmpBoth rfl fun t T _ cf => WP.block_nil ?_
  have K : Keeps [.eax] s t := T.keeps _
  exact ⟨h.rest K (by decide) (by decide) T.mem, K, T.mem, by simpa using cf⟩

theorem and15 (x : BitVec 32) : (x &&& 15 == 0) = decide (x.toNat % 16 = 0) := by
  have e : (x &&& 15).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← e]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toNat_eq h

theorem guard_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.InvBatchRt.guard s (Guarded args base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.guard
  -- `n_len % 16`.
  refine WP.seq (wp_movS h.gate.nArg.readSrc fun u₁ U₁ _ =>
    VG.Proof.Bignum.X86.CrtRt.wp_andZ rfl fun u U z => WP.block_nil ?_)
  have K : Keeps [.eax] s u := U₁.keeps.trans U.keeps
  have m : u.mem = s.mem := U.mem.trans U₁.mem
  have hu := h.rest K (by decide) (by decide) m
  rw [U₁.gpr, and15] at z
  refine WP.ite (decide ((args 7).toNat % 16 = 0)) z ?_ ?_
  · intro m16
    -- `128 ≤ n_len`.
    refine WP.seq (WP.mono (invCompare_ok hu hu.gate.nArg (limit := 128) (by decide)) fun v ⟨hv, kv, mv, _, cv⟩ => ?_)
    refine WP.ite (!decide ((args 7).toNat < 128)) (by simp only [eval, cv, Option.map_some]) ?_ ?_
    · intro big
      -- `p_len ≤ n_len / 2`.
      refine WP.seq (wp_movS hv.gate.nArg.readSrc fun w₁ W₁ _ => ?_)
      refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun w₂ W₂ => wp_addS rfl fun w₃ W₃ _ => ?_
      have K₃ : Keeps [.eax] v w₃ := (W₁.keeps.trans W₂.keeps).trans W₃.keeps
      have m₃ : w₃.mem = v.mem := by rw [W₃.mem, W₂.mem, W₁.mem]
      have h₃ := hv.rest K₃ (by decide) (by decide) m₃
      have half : (w₃.gpr .eax).toNat = (args 7).toNat / 2 + 1 := by
        rw [W₃.gpr, W₂.gpr, W₁.gpr, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := (args 7).isLt
        simp only [Nat.pow_one, show BitVec.toNat (1 : BitVec 32) = 1 from rfl]
        omega_using []
      refine wp_movS h₃.gate.pArg.readSrc fun w₄ W₄ _ => cmpBoth rfl fun w₅ W₅ _ c₅ => WP.block_nil ?_
      have K₅ : Keeps [.ecx] w₃ w₅ := W₄.keeps.trans (W₅.keeps _)
      have m₅ : w₅.mem = w₃.mem := W₅.mem.trans W₄.mem
      have h₅ := h₃.rest K₅ (by decide) (by decide) m₅
      have eax₄ : w₄.gpr .eax = w₃.gpr .eax := W₄.other _ (by decide)
      rw [W₄.gpr, eax₄, half] at c₅
      refine WP.ite (decide ((args 9).toNat < (args 7).toNat / 2 + 1)) c₅ ?_ ?_
      · intro py
        -- `q_len ≤ n_len / 2`.
        refine wp_movS h₅.gate.qArg.readSrc fun w₆ W₆ _ => cmpBoth rfl fun z Z zf cz => WP.block_nil ?_
        have Kz : Keeps [.ecx] w₅ z := W₆.keeps.trans (Z.keeps _)
        have mz : z.mem = w₅.mem := Z.mem.trans W₆.mem
        have eax₆ : w₆.gpr .eax = w₃.gpr .eax := by
          rw [W₆.other _ (by decide), K₅.1 _ (by decide)]
        rw [W₆.gpr, eax₆, half] at cz
        refine ⟨h₅.rest Kz (by decide) (by decide) mz,
          ((((K.mono (by decide)).trans (kv.mono (by decide))).trans (K₃.mono (by decide))).trans
            (K₅.mono (by decide))).trans (Kz.mono (by decide)),
          by rw [mz, m₅, m₃, mv, m], ?_⟩
        rw [cz]
        simp only [Eligible, of_decide_eq_true m16, true_and, of_decide_eq_true py]
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at big
        simp only [big, true_and]
      · intro py
        refine WP.mono (reject_ok h₅) fun z ⟨hz, kz, mz, cz⟩ => ?_
        refine ⟨hz, ((((K.mono (by decide)).trans (kv.mono (by decide))).trans (K₃.mono (by decide))).trans
          (K₅.mono (by decide))).trans (kz.mono (by decide)), by rw [mz, m₅, m₃, mv, m], ?_⟩
        rw [cz]
        simp only [Eligible, of_decide_eq_false py, false_and, and_false, decide_false]
    · intro small
      refine WP.mono (reject_ok hv) fun z ⟨hz, kz, mz, cz⟩ => ?_
      refine ⟨hz, ((K.mono (by decide)).trans (kv.mono (by decide))).trans (kz.mono (by decide)),
        by rw [mz, mv, m], ?_⟩
      rw [cz]
      simp only [Bool.not_eq_false', decide_eq_true_eq] at small
      simp only [Eligible, show ¬ 128 ≤ (args 7).toNat by omega_using [small], false_and, and_false, decide_false]
  · intro no
    refine WP.mono (reject_ok hu) fun z ⟨hz, kz, mz, cz⟩ => ?_
    refine ⟨hz, (K.mono (by decide)).trans (kz.mono (by decide)), by rw [mz, m], ?_⟩
    rw [cz]
    simp only [Eligible, of_decide_eq_false no, false_and, decide_false]

end VG.Proof.Rsa.X86.CrtValuesRt

end

end

/-! # Correct selection and fallback for the three public RSA widths -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)

 theorem inverseDispatch_ok [VG.Proof.Rsa.X86.BatchLaw] {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.dispatch lay VG.Impl.Rsa.X86.CrtValuesRt.fallback) s
      (InvPost base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.dispatch
  refine WP.seq (WP.mono (guard_ok h) fun u g => ?_)
  refine WP.mono (Q := InvPost base size len P Q u)
    (WP.ite (decide (Eligible args)) g.cf ?_ ?_)
    fun t post => post.pre_rest g.keeps (by decide) g.mem
  · intro yes
    obtain ⟨m16, big, pb, qb⟩ := of_decide_eq_true yes
    obtain ⟨a, al, aw, arg⟩ := g.input.ws.lenArg
    change kw a = kw len at aw
    have eq : BitVec.ofNat 32 a = args 7 := Option.some.inj (arg.readSrc.symm.trans g.input.gate.nArg.readSrc)
    have ae := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [al])] at ae
    have nwl : VG.Proof.Rsa.X86.InvBatchRt.nw len = a / 8 := by
      have aw' := aw
      simp only [kw, Spec.Rsa.modulusWords] at aw'
      simp only [VG.Proof.Rsa.X86.InvBatchRt.nw, kw, Spec.Rsa.modulusWords]; omega_using [m16, ae, aw']
    exact inverseBodyRt_ok g.input (by omega_using [big, ae, nwl]) (by omega_using [m16, ae, nwl]) (by omega_using [m16, pb, ae, nwl]) (by omega_using [m16, qb, ae, nwl])
  · intro _; exact inverseFallback_ok g.input

end VG.Proof.Rsa.X86.CrtValuesRt

end

end

/-! # CRT parameter calculation at a run-time width: the checks

`CrtValues`' checks and the binary inversion's setup (`checksA_ok`), then the
inversion, its check and the mask releasing the results (`checksB_ok`), on
`RtWs` at the width `kw len`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs andS)
open VG.Impl.Rsa.X86.KeyRt (Lay)
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append bank invArrs invSlots rtSlots)
open VG.Proof.Rsa.X86.KeyRt

/-- The values the arithmetic works on. -/
structure Geometry where
  base : Addr
  size : Nat
  P : Nat
  Q : Nat
  D : Nat
  N : Nat

def Geometry.M (g : Geometry) : Nat := 2 * (g.P / 2) + 1

def zeroC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 23]

/-- The arrays still zero after the product `p q`. -/
def zeroCk : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

structure StC (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  podd : slot s.mem g.base sPodd = g.P % 2
  p : num s.mem g.base (kw len) aP = g.P
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  n : num s.mem g.base (kw len) aDQ = g.N
  prod : val32 s.mem g.base (arr (kw len) aDR2) (2 * kw len) = g.P * g.Q
  zeros : ∀ j ∈ zeroCk, num s.mem g.base (kw len) j = 0

def checksA : List (Prog isa) := [VG.Impl.Rsa.X86.WordModRt.eqWide lay sE1 aDR2 aDQ] ++ invSetup

structure StI (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  podd : slot s.mem g.base sPodd = g.P % 2
  e1 : slot s.mem g.base sE1 = if g.P * g.Q = g.N then 1 else 0
  p : num s.mem g.base (kw len) aP = g.P
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  u : num s.mem g.base (kw len) 0 = g.Q
  v : num s.mem g.base (kw len) 1 = g.M
  x₁ : num s.mem g.base (kw len) 2 = 1
  x₂ : num s.mem g.base (kw len) 3 = 0
  m : num s.mem g.base (kw len) aM = g.M
  nm : num s.mem g.base (kw len) aNM + g.M = 2 ^ (32 * kw len)
  zero : num s.mem g.base (kw len) aZero = 0
  one : num s.mem g.base (kw len) aOne = 1

theorem checksA_ok {g : Geometry} {len : Nat} {s : State} (h : StC g len s) :
    WP isa (seqs (checksA)) s fun t =>
      StI g len t ∧
      Keep g.base (kw len) [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have h1 := h.ws
  unfold checksA invSetup
  simp only [List.cons_append, List.nil_append]
  obtain fit := fun j (hj : j < nArr) => h1.ws.fit64 (j := j) hj
  have h2 := h1
  obtain k2 : Keep g.base (kw len) [] [] s.mem s.mem := Keep.refl _ _ _ _ _
  obtain r2 : Keeps [] s s := Keeps.refl _ _
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.eqWide_ok h2 (sl := sE1) (o := aDR2) (n := aDQ) (by decide) (by decide)
    (by decide)) fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := 0) (a := aQ) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aM) (a := aP) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (orOne_ok h5 (by decide)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h6 (o := 1) (a := aM) (by decide) (by decide) (by decide))
    fun t7 ⟨h7, k7, e7, r7, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (setOne_ok h7 (j := 2) (by decide)) fun t8' ⟨h8', k8', e8', r8'⟩ => ?_)
  refine WP.mono (setOne_ok h8' (j := aOne) (by decide)) fun t8 ⟨h8, k8, e8, r8⟩ => ?_
  refine WP.mono (sub3_ok h8 (o := aNM) (a := aZero) (b := aM) (by decide) (by decide) (by decide)) fun t ⟨ht, k9, e9, b9, r9⟩ => ?_
  obtain K : Keep g.base (kw len) [aT1, 0, aM, 1, 2, aOne, aNM] [sT, sE1, sE2] s.mem t.mem :=
    k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans (k7.mono.trans
      (k8'.mono.trans (k8.mono.trans k9.mono)))))))
  obtain R : Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t :=
    (r2.mono (by decide)).trans ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans
      ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans ((r8'.mono (by decide)).trans
        ((r8.mono (by decide)).trans (r9.mono (by decide)))))))))
  obtain z0 : ∀ j ∈ zeroCk, num s.mem g.base (kw len) j = 0 := fun j hj => h.zeros j hj
  obtain K1 : ∀ j, j < nArr → j ∉ [aT1, 0, aM, 1, 2, aOne, aNM] →
      num t.mem g.base (kw len) j = num s.mem g.base (kw len) j := fun j hj hn => by
    rw [K.num (fun k hk e => hn (by subst e; exact hk)) (by decide) (fit j hj)]
  -- `M`.
  obtain M5 : num t5.mem g.base (kw len) aM = g.P := by
    rw [e5, k4.num (by decide) (by simp) (fit _ (by decide)), k3.num (by decide) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)), h.p]
  obtain M6 : num t6.mem g.base (kw len) aM = g.M := by rw [e6, M5]; rfl
  obtain M8 : num t8.mem g.base (kw len) aM = g.M := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), M6]
  obtain Z8 : num t8.mem g.base (kw len) aZero = 0 := by
    rw [k8.num (by decide) (by simp) (fit _ (by decide)), k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]
  refine ⟨?_, K, R⟩
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K.slot (by decide) (by decide), h.podd]
  · rw [k9.slot (by decide) (by simp), k8.slot (by decide) (by simp), k8'.slot (by decide) (by simp),
      k7.slot (by decide) (by simp), k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), e3, h.prod, h.n]
  · rw [K1 _ (by decide) (by decide), h.p]
  · rw [K1 _ (by decide) (by decide), h.q]
  · rw [K1 _ (by decide) (by decide), h.d]
  · rw [K.word (by simp only [S]; omega_arith) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)),
      k8'.num (by decide) (by simp) (fit _ (by decide)), k7.num (by decide) (by simp) (fit _ (by decide)),
      k6.num (by decide) (by simp) (fit _ (by decide)), k5.num (by decide) (by simp) (fit _ (by decide)), e4,
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      h.q]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)),
      k8'.num (by decide) (by simp) (fit _ (by decide)), e7, M6]
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), k8.num (by decide) (by simp) (fit _ (by decide)), e8',
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]
  · rw [K1 _ (by decide) (by decide)]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), M8]
  · rw [Z8, M8] at e9
    have : 0 < g.M := by unfold Geometry.M; omega_arith
    obtain l := val32_lt t.mem g.base (arr (kw len) aNM) (kw len)
    rcases (by omega_arith : (t.gpr .ebx).toNat = 0 ∨ (t.gpr .ebx).toNat = 1) with e | e <;> rw [e] at e9 <;> omega_arith
  · rw [K1 _ (by decide) (by decide)]; exact z0 _ (by decide)
  · rw [k9.num (by decide) (by simp) (fit _ (by decide)), e8, k8'.num (by decide) (by simp) (fit _ (by decide)),
      k7.num (by decide) (by simp) (fit _ (by decide)), k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
      k3.num (by decide) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      z0 _ (by decide)]


def checksB : List (Prog isa) := [inverseChoice, VG.Impl.Rsa.X86.KeyRt.eqS lay sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE3),
  VG.Impl.Rsa.X86.KeyRt.copy lay aDQ aD, VG.Impl.Rsa.X86.KeyRt.copy lay aDD aP, .block (VG.Impl.Rsa.X86.KeyRt.clrLow lay aDD)]

/-- The mask of the checks, from `p`, `q`, `n` and the gcd `V`. -/
abbrev maskOf := VG.Proof.Rsa.CrtValues.maskOfP

def InverseResult (g : Geometry) (len : Nat) (m : Mem) : Prop :=
  ∃ V, slot m g.base sMask = (if maskOf g.P g.Q g.N V then 1 else 0) ∧
    (1 < g.M → V = Nat.gcd g.Q g.M ∧
      (g.M : Int) ∣ (num m g.base (kw len) 3 : Int) * g.Q - V ∧ num m g.base (kw len) 3 < g.M)

/-- Before the division of `d` by `p - 1`. -/
structure StD (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  dq : num s.mem g.base (kw len) aDQ = g.D
  dd : num s.mem g.base (kw len) aDD = 2 * (g.P / 2)
  mask : InverseResult g len s.mem

theorem checksB_ok [VG.Proof.Rsa.X86.BatchLaw] {g : Geometry} {len : Nat} {s : State} (h : StI g len s) {args : Nat → BitVec 32}
    (gate : InvGate args g.base g.size g.P g.Q s) :
    WP isa (seqs (checksB)) s fun t => StD g len t ∧
      VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
        (VG.Proof.Rsa.X86.Keys.ranges (kw len) (invOut ++ [aDQ, aDD]) (invSlots ++ rtSlots ++ [sT, sE3, sMask])) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have hw := h.ws
  obtain fit := fun j (hj : j < nArr) => hw.ws.fit64 (j := j) hj
  obtain inside := fun j (hj : j < nArr) => Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end hj) hw.ws.fits
  have room := gate.room
  obtain nowrap : g.size ≤ 2 ^ 64 := by have := hw.ws.workspace.nowrap; omega_using [this]
  have hdrLe : hdr ≤ g.size := hw.ws.hdr_le
  unfold checksB
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  obtain input : InvInput args g.base g.size len g.P g.Q s :=
    ⟨h.ws,gate,h.u,h.m,h.nm,h.zero,by simp only [bank]; rw [h.u,h.v,h.x₁,h.x₂]; rfl⟩
  refine WP.mono (inverseDispatch_ok input) fun t1 ⟨h1,k1,r1,inv⟩ => ?_
  have I : 1<g.M → num t1.mem g.base (kw len) 1=Nat.gcd g.Q g.M ∧
      (g.M : Int)∣(num t1.mem g.base (kw len) 3 : Int)*g.Q-num t1.mem g.base (kw len) 1 ∧
      num t1.mem g.base (kw len) 3<g.M := inv
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h1 (d := sE3) (a := 1) (b := aOne) (t := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  obtain one1 : num t1.mem g.base (kw len) aOne = 1 := by
    rw [outsS_num k1 room (by decide) (by decide) (inside _ (by decide)) nowrap, h.one]
  rw [one1] at e2
  obtain sl : ∀ d, d + 4 ≤ hdr → d % 4 = 0 → 100 ≤ d → d ∉ [sT, sE3, sOdd, sB, sC] →
      slot t2.mem g.base d = slot s.mem g.base d := fun d hd h4 h100 hn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp only [sT, sE3, sOdd, sB, sC, hdr] at hn hd
    rw [k2.slot (by simp only [hdr]; omega_arith) (by simp only [sT, sE3]; simp; omega_arith),
      outsS_slot k1 room (by simp only [hdr]; omega_arith) hdrLe
        (by simp only [invSlots, rtSlots, sOdd, sB, sC]; simp; omega_arith)]
  rw [wp_seqs_cons (List.cons_ne_nil _ _), List.append_assoc]
  refine WP.block_append ?_
  refine WP.mono (andS_ok h2 (d := sMask) (a := sPodd) (b := sE1) (by decide) (by decide) (by decide)
    (by rw [sl _ (by decide) (by decide) (by decide) (by decide), h.podd]; omega_arith) (by rw [sl _ (by decide) (by decide) (by decide) (by decide), h.e1]; split <;> omega_arith)
    ) fun t3a ⟨h3a, k3a, m3a, r3a⟩ => ?_
  have h3b := h3a
  obtain k3b : Keep g.base (kw len) [] [sMask] t3a.mem t3a.mem := Keep.refl _ _ _ _ _
  obtain r3b : Keeps [] t3a t3a := Keeps.refl _ _
  have m3b := m3a
  refine WP.mono (andS_ok h3b (d := sMask) (a := sMask) (b := sE3) (by decide) (by decide) (by decide)
    (by rw [m3b]; split <;> omega_arith)
    (by rw [k3b.slot (by decide) (by decide), k3a.slot (by decide) (by decide), e2]; split <;> omega_arith)
    ) fun t3 ⟨h3, k3, m3, r3⟩ => ?_
  obtain K3 : Keep g.base (kw len) [] [sMask] t2.mem t3.mem := k3a.trans (k3b.trans k3)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (o := aDQ) (a := aD) (by decide) (by decide) (by decide))
    fun t4 ⟨h4, k4, e4, r4, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (o := aDD) (a := aP) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, k5, e5, r5, top5⟩ => ?_
  refine WP.mono (clrLow_ok h5 (by decide)) fun t ⟨h6, k6, e6, r6, top6⟩ => ?_
  -- The count, through every step.
  obtain K₂ : Keep g.base (kw len) (invOut ++ [aDQ, aDD]) (invSlots ++ rtSlots ++ [sT, sE3, sMask]) t1.mem t.mem :=
    k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans k6.mono)))
  obtain K : VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
      (VG.Proof.Rsa.X86.Keys.ranges (kw len) (invOut ++ [aDQ, aDD]) (invSlots ++ rtSlots ++ [sT, sE3, sMask])) s.mem t.mem :=
    (k1.mono (ranges_sub (by decide) (by decide))).trans (VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs K₂)
  obtain R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3a.mono (by decide)).trans ((r3b.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans (r6.mono (by decide))))))))
  obtain tr : ∀ j, j < nArr → j ∉ invOut ++ [aDQ, aDD] →
      num t.mem g.base (kw len) j = num s.mem g.base (kw len) j := fun j hj hn =>
    outsS_num K room (fun k hk e => hn (by subst e; exact hk)) (by decide) (inside j hj) nowrap
  obtain fDD := fit aDD (by decide)
  have hS : S (kw len) = 4 * ((kw len) + 2) := rfl
  refine ⟨?_, K, R⟩
  refine ⟨h6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tr _ (by decide) (by decide), h.q]
  · rw [tr _ (by decide) (by decide), h.d]
  · rw [top6, top5,
      k4.word (by omega_arith) (by decide) (by simp) fDD, K3.word (by omega_arith) (by simp) (by decide) fDD,
      k2.word (by omega_arith) (by decide) (by decide) fDD, outsS_word k1 room (by omega_arith) (by decide) (by decide) (inside _ (by decide)) nowrap, h.ddTop]
  · rw [k6.num (by decide) (by simp) (fit _ (by decide)),
      k5.num (by decide) (by simp) (fit _ (by decide)), e4, K3.num (by simp) (by decide) (fit _ (by decide)),
      k2.num (by decide) (by decide) (fit _ (by decide)),
      outsS_num k1 room (by decide) (by decide) (inside _ (by decide)) nowrap, h.d]
  · rw [e6, e5, k4.num (by decide) (by simp) (fit _ (by decide)),
      K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide)),
      outsS_num k1 room (by decide) (by decide) (inside _ (by decide)) nowrap, h.p]
  · have x3 : num t.mem g.base (kw len) 3 = num t1.mem g.base (kw len) 3 := by
      rw [k6.num (by decide) (by simp) (fit _ (by decide)),
        k5.num (by decide) (by simp) (fit _ (by decide)), k4.num (by decide) (by simp) (fit _ (by decide)),
        K3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by decide) (by decide) (fit _ (by decide))]
    refine ⟨num t1.mem g.base (kw len) 1, ?_, fun hM => by rw [x3]; exact I hM⟩
    rw [k6.slot (by decide) (by simp), k5.slot (by decide) (by simp),
      k4.slot (by decide) (by simp), m3, m3b, k3a.slot (e := sE3) (by decide) (by decide), e2,
      sl sPodd (by decide) (by decide) (by decide) (by decide), sl sE1 (by decide) (by decide) (by decide) (by decide),
      h.podd, h.e1]
    simp only [maskOf, VG.Proof.Rsa.CrtValues.maskOfP]
    by_cases a : g.P % 2 = 1 <;> by_cases b : g.P * g.Q = g.N <;>
      by_cases d : num t1.mem g.base (kw len) 1 = 1 <;> simp [a, b, d]

end VG.Proof.Rsa.X86.CrtValuesRt
