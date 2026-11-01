module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Rsa.X86.InvGate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Spec.RsaKeyGen.Contract

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Verified
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Weierstrass.MontContract

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
  have far := hx _ (List.mem_append_right _ (List.mem_singleton_self _))
  have := (x - B).isLt
  unfold ofs at far
  exact room.2.2 x (by simp only [Region.Contains]; omega) hb

/-- An array of the working space outside the frame. -/
theorem outsS_num {sp : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : OutsS B sp (ranges w js ds) m m') (room : Room sp B Z) {j : Nat} (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (inside : arr w j + S w ≤ Z) (nowrap : Z ≤ 2 ^ 64) :
    num m' B w j = num m B w j := by
  have hS : 4 * w ≤ S w := by simp only [S]; omega
  refine Outs.val32 (outsS_ws h room) (fun r hr => ?_) (by omega)
  rcases List.mem_append.mp hr with hr | hr
  · simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
    · have := VG.Proof.Rsa.X86.Keys.arr_disj (w := w) (hj k hk); dsimp only; omega
    · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega
  · obtain rfl := List.mem_singleton.mp hr; dsimp only; omega

/-- A word of an array of the working space outside the frame. -/
theorem outsS_word {sp : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : OutsS B sp (ranges w js ds) m m') (room : Room sp B Z) {j i : Nat} (hi : 4 * i + 4 ≤ S w)
    (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (inside : arr w j + S w ≤ Z) (nowrap : Z ≤ 2 ^ 64) :
    VG.Proof.Mont.w32 m' B (arr w j + 4 * i) = VG.Proof.Mont.w32 m B (arr w j + 4 * i) := by
  have := Outs.val32 (k := 1) (d := arr w j + 4 * i) (outsS_ws h room) (fun r hr => ?_) (by omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  rcases List.mem_append.mp hr with hr | hr
  · simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
    · have := VG.Proof.Rsa.X86.Keys.arr_disj (w := w) (hj k hk); dsimp only; omega
    · have := hd d hd'; have : hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega
  · obtain rfl := List.mem_singleton.mp hr; dsimp only; omega

/-- A header word outside the frame. -/
theorem outsS_slot {sp : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : OutsS B sp (ranges w js ds) m m') (room : Room sp B Z) {e : Nat} (he : e + 4 ≤ hdr)
    (hZ : hdr ≤ Z) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) : slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) (outsS_ws h room) (fun r hr => ?_) (by simp only [hdr] at he; omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  rcases List.mem_append.mp hr with hr | hr
  · simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
    · have : hdr ≤ arr w k := Nat.le_add_right _ _; dsimp only; omega
    · exact hd d hd'
  · obtain rfl := List.mem_singleton.mp hr; dsimp only; omega

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
  have hv := hu.keep V.keeps (by decide) (by decide) (by rw [V.mem]; exact Outside.refl _ _ _ _)
  refine wp_addS (readSrc_sc hv.ws.workspace (by unfold hdr at hsl head; omega)) fun x X _ => ?_
  have hx := hu.keep (V.keeps.trans X.keeps) (by decide) (by decide)
    (by rw [X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine wp_addS (readSrc_sc hx.ws.workspace (by unfold hdr at hsl head; omega)) fun y Y _ => ?_
  have KY : Keeps [.ecx] u y := V.keeps.trans (X.keeps.trans Y.keeps)
  have hy := hu.keep KY (by decide) (by decide) (by rw [Y.mem, X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeLow_ok hy hj (by rw [Rt.PtrAt, KY.1 _ (by decide)]; exact p))
    fun t ⟨ht, F, Vt, Kt, _⟩ => ?_
  have my : y.mem = s.mem := by rw [Y.mem, X.mem, V.mem, m]
  rw [my] at F Vt
  refine ⟨ht, F, ?_, ((K.mono (by decide)).trans (KY.mono (by decide))).trans (Kt.mono (by decide))⟩
  intro bit one
  have low := VG.Proof.Rsa.X86.KeyRt.low_word (B := B) (m := s.mem) (j := j) positive
  have sx : (x.mem.readW (off B sl) 32).toNat = slot s.mem B sl := by rw [X.mem, V.mem, m]
  have sv : (v.mem.readW (off B sl) 32).toNat = slot s.mem B sl := by rw [V.mem, m]
  rw [Vt, Y.gpr, X.gpr, V.gpr, m, BitVec.toNat_add, BitVec.toNat_add, sx, sv, ← low]
  rcases (show slot s.mem B sl = 0 ∨ slot s.mem B sl = 1 by omega) with e | e
  · rw [e]; omega
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
  have fit := fun j (hj : j < N) => h.ws.fit64 (j := j) hj
  unfold modulusAbove
  rw [VG.Proof.Rsa.X86.Keys.wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqSFast_ok h (d := sOne) (a := aM) (b := 2) (by unfold aM; omega)
    (by omega) (by decide)) fun u ⟨hu, ku, fu, ru⟩ => ?_
  have mu : num u.mem B (kw len) aM = num s.mem B (kw len) aM :=
    ku.num (by decide) (by decide) (fit _ (by unfold aM; omega))
  rw [two] at fu
  rw [VG.Proof.Rsa.X86.Keys.wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (addLowTwice_ok hu (j := aM) (sl := sOne) (by unfold aM; omega) (by decide))
    fun v ⟨hv, kv, ev, rv⟩ => ?_
  have ev' := ev (by rw [fu]; split <;> omega) (by rw [fu]; split <;> simp_all)
  rw [mu, fu] at ev'
  have mv : num v.mem B (kw len) aM = (if num s.mem B (kw len) aM = 1 then 3 else num s.mem B (kw len) aM) := by
    rw [ev']; split <;> simp_all
  rw [VG.Proof.Rsa.X86.Keys.wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok hv (o := 1) (a := aM) (by omega) (by unfold aM; omega)
    (by decide)) fun w ⟨hw, kw', ew, rw', _⟩ => ?_
  have mw : num w.mem B (kw len) aM = num v.mem B (kw len) aM :=
    kw'.num (by decide) (by decide) (fit _ (by unfold aM; omega))
  have zw : num w.mem B (kw len) aZero = 0 := by
    rw [kw'.num (by decide) (by decide) (fit _ (by unfold aZero; omega)),
      kv.num (by decide) (by decide) (fit _ (by unfold aZero; omega)),
      ku.num (by decide) (by decide) (fit _ (by unfold aZero; omega)), zero]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok hw (o := aNM) (a := aZero) (b := aM) (by unfold aNM; omega)
    (by unfold aZero; omega) (by unfold aM; omega)) fun t ⟨ht, kt, et, bt, rt⟩ => ?_
  have mt : num t.mem B (kw len) aM = num w.mem B (kw len) aM :=
    kt.num (by decide) (by decide) (fit _ (by unfold aM; omega))
  have one : num t.mem B (kw len) 1 = num w.mem B (kw len) 1 :=
    kt.num (by decide) (by decide) (fit _ (by omega))
  have pos : 0 < num w.mem B (kw len) aM := by rw [mw, mv]; split <;> omega
  refine ⟨ht, ?_, ((ru.mono (by decide)).trans ((rv.mono (by decide)).trans (rw'.mono (by decide)))).trans rt,
    by rw [mt, mw, mv], by rw [one, ew, mt, mw], ?_⟩
  · exact (ku.mono (by decide) (by decide)).trans ((kv.mono (by decide) (by decide)).trans
      ((kw'.mono (by decide) (by decide)).trans (kt.mono (by decide) (by decide))))
  · rw [mt]
    rw [zw, Nat.zero_add] at et
    have : (t.gpr .ebx).toNat = 1 := by
      rcases (show (t.gpr .ebx).toNat = 0 ∨ (t.gpr .ebx).toNat = 1 by omega) with e | e
      · rw [e, Nat.mul_zero] at et; omega
      · exact e
    rw [et, this, Nat.mul_one]

/-! ## The call -/

open VG.Proof.RsaKeyGen.X86.KeyRuntime (invArgs invEntry InvArguments invEntry_arg invEntry_frame
  invEntry_pre code_noSp code_stack rtWs_keepBelow)

/-- The words of working space the callee uses, for a length argument `a`. -/
abbrev invWords (a : Nat) : Nat := 35 + 15 * ((a + 7) / 8)

/-- What the callee writes lies in the inverse's arrays and header words. -/
theorem writes_ranges {a W i : Nat} (hka : kw a = W) (hw : Spec.RsaKeyGen.inverseWrites a i) :
    ¬ ∀ r ∈ ranges W invArrs invSlots, i < r.1 ∨ r.1 + r.2 ≤ i := by
  intro out
  simp only [kw, Spec.Rsa.modulusWords] at hka
  unfold Spec.RsaKeyGen.inverseWrites Spec.RsaKeyGen.inverseBytes at hw
  rcases hw with ⟨lo, hi⟩ | ⟨j, hj, lo, hi⟩
  · have h0 := out (VG.Impl.Rsa.X86.Keys.sOdd, 4) (by simp [ranges])
    have h1 := out (VG.Impl.Rsa.X86.Keys.sB, 4) (by simp [ranges])
    have h2 := out (VG.Impl.Rsa.X86.Keys.sC, 4) (by simp [ranges])
    simp only [VG.Impl.Rsa.X86.Keys.sOdd, VG.Impl.Rsa.X86.Keys.sB, VG.Impl.Rsa.X86.Keys.sC] at h0 h1 h2
    omega
  · have mem : j ∈ invArrs := by
      simp only [invArrs, VG.Impl.Rsa.X86.Keys.aT1, VG.Impl.Rsa.X86.Keys.aT2, VG.Impl.Rsa.X86.Keys.aT3,
        VG.Impl.Rsa.X86.Keys.aT4, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have H := out (arr W j, S W) (List.mem_append_left _ (List.mem_map_of_mem mem))
    simp only [arr, S, hdr] at H
    have e : 8 * ((a + 7) / 8) + 8 = 4 * (W + 2) := by omega
    rw [e] at lo hi
    have := Nat.add_mul j 1 (4 * (W + 2))
    omega

/-- What `vg_rsa_keygen_inverse`'s postcondition tells its caller. -/
theorem inversePost_of {s t : State} (post : VG.Proof.RsaKeyGen.X86.Inverse.contract.post s t) :
    (∀ i, i < VG.Proof.RsaKeyGen.X86.Inverse.size s →
      ¬ Spec.RsaKeyGen.inverseWrites (VG.Proof.RsaKeyGen.X86.Inverse.len s) i →
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
    Spec.RsaKeyGen.inverseContract, Spec.RsaKeyGen.inverseSig, abi, argSlots, argVal, argBytes] at post
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
  omega

theorem size (C : CallAt B Z len a u) : 8 * invWords a ≤ Z := by
  have fits := C.fits
  simp only [arr, S, hdr, kw, Spec.Rsa.modulusWords] at fits
  unfold invWords
  omega

theorem ptrBound (C : CallAt B Z len a u) : B.toNat < 2 ^ 32 := by
  have := C.fits
  have := C.ws.ws.workspace.nowrap
  simp only [arr, hdr] at *
  omega

theorem lenLow (C : CallAt B Z len a u) : 1 ≤ a := by
  have wpos : 0 < kw a := by rw [C.words]; exact C.ws.kw_pos
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
  have pre := invEntry_pre C.args nowrap C.lenLow C.lenLe rfl C.fits C.room.1 C.room.2.2
    (by rw [C.words]; exact C.odd) (by rw [C.words]; exact C.large) (by rw [C.words]; exact C.v)
    (by rw [C.words]; exact C.x₁) (by rw [C.words]; exact C.x₂) (by rw [C.words]; exact C.negated)
    (by rw [C.words]; exact C.zero)
  have size := C.size
  have wsIn : InRegions u.wr B (8 * invWords a) :=
    ⟨_, C.ws.ws.workspace.wr, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
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
    (by decide : Reg.esp ∉ invArgs) (by rw [code_stack]; change 32 ≤ _; omega) C.callPre ?_
  intro t rdT wrT saved frame post
  obtain ⟨e₂, mem₂, post⟩ := post
  rw [CallAt.entry_eq B a u] at post
  obtain ⟨inside, gcd, bezout, lt⟩ := inversePost_of post
  have fit16 : 16 ≤ (u.gpr .esp).toNat := by omega
  have wordsBound : invWords a < 2 ^ 32 := by have := C.lenLe; omega
  have arg0 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 0) (by decide)
  have arg1 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 1) (by decide)
  have arg2 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 2) (by decide)
  simp only [↓reduceIte, Nat.reduceEqDiff] at arg0 arg1 arg2
  have baseE : VG.Proof.RsaKeyGen.X86.Inverse.base (invEntry B (8 * invWords a) u) = B := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.base
    rw [arg0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt B.isLt
  have sizeE : VG.Proof.RsaKeyGen.X86.Inverse.size (invEntry B (8 * invWords a) u) = 8 * invWords a := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.size
    rw [arg1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordsBound]
  have lenE : VG.Proof.RsaKeyGen.X86.Inverse.len (invEntry B (8 * invWords a) u) = a := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.len
    rw [arg2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := C.lenLe; omega)]
  simp only [baseE, sizeE, lenE, hka, mem₂] at inside gcd bezout lt
  have FE := invEntry_frame (B := B) (L := 8 * invWords a) fit16
  have farU : (⟨B, Z⟩ : Region).Disjoint (below (u.gpr .esp) 16) :=
    far.sub_right (below_sub (by decide) lowSp)
  have entryNum {j : Nat} (hj : j < 15) :
      num (invEntry B (8 * invWords a) u).mem B (kw len) j = num u.mem B (kw len) j :=
    VG.Proof.RsaKeyGen.X86.KeyRuntime.frame_num FE farU nowrap
      (Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end hj) (by have := C.fits; rwa [hka] at this))
  rw [entryNum (j := 0) (by decide), entryNum (j := 8) (by decide)] at gcd bezout
  rw [entryNum (j := 8) (by decide)] at lt
  have Kt : Keeps [.eax, .ecx, .edx] u t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp [calleeSaved] at hr ⊢
  have stackFrame : Frame [⟨B, Z⟩, below (u.gpr .esp) 52] u.mem t.mem := by
    refine frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix size⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [code_stack]
      exact below_sub (by decide) lowSp
  refine ⟨rtWs_keepBelow h Kt (by decide) (by decide) stackFrame lowSp
    (by have := C.room.2.1; change _ + 8 + 4 * 7 ≤ _; omega)
    (by have := C.room.2.1; change _ + 8 + 4 * 14 ≤ _; omega), ?_, gcd, bezout, lt, Kt⟩
  intro x hx hz
  by_cases hin : (⟨B, 8 * invWords a⟩ : Region).Contains x 1
  · have hi : ofs B x < 8 * invWords a := by
      simp only [Region.Contains] at hin
      unfold ofs
      omega
    have changed := inside (ofs B x) hi fun c => writes_ranges hka c hx
    have back : B + BitVec.ofNat 64 (ofs B x) = x := by
      unfold ofs
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
      exact BitVec.sub_add_cancel x B
    rw [back] at changed
    rw [changed]
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
  have fit₁ : 16 ≤ (u₁.gpr .esp).toNat := by have := C₁.room.1; omega
  have fit₂ : 16 ≤ (u₂.gpr .esp).toNat := by have := C₂.room.1; omega
  have sa := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * invWords a) C₁.args fit₁ hi
  have ta := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * invWords a) C₂.args fit₂ hi
  have esp : (invEntry B (8 * invWords a) u₁).gpr .esp = (invEntry B (8 * invWords a) u₂).gpr .esp := by
    change (pushed invArgs u₁).callEntry.gpr .esp = (pushed invArgs u₂).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', sp]
  sig_pub [VG.Proof.RsaKeyGen.X86.Inverse.contract, VG.Proof.RsaKeyGen.X86.Inverse.inverseStack,
    Spec.RsaKeyGen.inverseContract, Spec.RsaKeyGen.inverseSig, abi, argSlots, argVal, argBytes]
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
  have e₁ := CallAt.entry_eq B a u₁
  have e₂ := CallAt.entry_eq B a u₂
  rw [s₁] at e₁
  rw [s₂] at e₂
  rw [e₁, e₂]
  exact C₁.pub C₂ (s₁.trans s₂.symm)

end VG.Proof.Rsa.X86.CrtValuesRt
