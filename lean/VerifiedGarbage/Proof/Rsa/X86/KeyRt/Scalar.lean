module

import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Omega
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.X86.KeyBits

/-! ### `Rsa.X86.KeyRt.Word`, which this module and modules that import it used -/

section

/-! # The low words of the key workspace's arrays at a run-time width

Through a pointer to the array in `eax` (`arrPtr`): its low word replaced
(`storeLow_ok`), and with it `setOne_ok`, `orOne_ok`, `clrLow_ok`,
`addLow_ok`; and the low bit into a header word (`bitOf_ok`). Each states
what `Keys`' per-width lemma does.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot)
open VG.Proof.Rsa.KeyBits32

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `[eax] = ecx` for `eax` at array `j`. -/
theorem storeLow_ok {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) (p : PtrAt s B .eax (arr (kw len) j)) :
    WP isa (.block [.store (at_ .eax 0) .ecx]) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = (s.gpr .ecx).toNat + 2 ^ 32 * (num s.mem B (kw len) j / 2 ^ 32) ∧
      Keeps [] s t ∧ w32 t.mem B (arr (kw len) j + 4 * kw len) = w32 s.mem B (arr (kw len) j + 4 * kw len) := by
  have fit := h.ws.arr_fit hj
  have positive := h.kw_pos
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  refine wp_storeS (ea_ptr h.rt p (d := 0) (by omega_using [fit])) (ws_write h.rt (y := arr (kw len) j + 0) (n := 4) (by omega_using [fit]))
    fun t T => WP.block_nil ?_
  rw [Nat.add_zero] at T
  have outside := writeW32_outside s.mem B (d := arr (kw len) j) (s.gpr .ecx) (by omega_using [fit, nw])
  refine ⟨h.keep (T.keeps []) (by decide) (by decide) (by rw [T.mem]; exact outside.mono (Nat.zero_le _) (by omega_using [fit])),
    ?_, ?_, T.keeps [], ?_⟩
  · rw [T.mem]
    exact Keep.of_arr (d := 0) (by simpa using outside) (by unfold S; omega_using []) (by simp)
  · rw [T.mem]
    exact VG.Proof.Rsa.KeyWorkspace.num_write0 _ _ positive (by change arr (kw len) j + 4 * kw len ≤ 2 ^ 64; omega_using [fit, nw]) _
  · rw [T.mem]; exact outside.w32 (by omega_using [positive]) (by omega_using [fit, nw])

/-- The array's low word, through `eax`. -/
theorem lowSrc {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) (p : PtrAt s B .eax (arr (kw len) j)) :
    readSrc s (.mem (at_ .eax 0)) = some (s.mem.readW (off B (arr (kw len) j)) 32) := by
  have fit := h.ws.arr_fit hj
  simp only [S] at fit
  rw [readSrc_ptr h.rt p (d := 0) (by omega_using [fit]), Nat.add_zero]

/-- The low word as the number's low 32 bits. -/
theorem low_word {m : Mem} {w j : Nat} (hw : 0 < w) :
    num m B w j % 2 ^ 32 = (m.readW (off B (arr w j)) 32).toNat :=
  VG.Proof.Rsa.KeyWorkspace.num_mod32 m B (j := j) hw

/-- The context, the pointer and the arguments after `arrPtr L .eax j .edx`. -/
theorem lowPtr_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N)
    (k : ∀ u, RtWs L u B Z len N → Keeps [.eax, .edx] s u → u.mem = s.mem → PtrAt u B .eax (arr (kw len) j) →
      WP isa (.block is) u Q) :
    WP isa (.block (arrPtr L .eax j .edx ++ is)) s Q := by
  have fit := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (by decide) (by decide) (by omega_using [fit, nw]) fun u K m p _ => ?_
  exact k u (h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)) K m p

theorem setOne_ok {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) :
    WP isa (.block (setOne L j)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = 1 + 2 ^ 32 * (num s.mem B (kw len) j / 2 ^ 32) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  unfold setOne
  refine lowPtr_ok h hj fun u hu K m p => wp_movS rfl fun v V _ => ?_
  have hv := hu.keep V.keeps (by decide) (by decide) (by rw [V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeLow_ok hv hj (by rw [PtrAt, V.other _ (by decide)]; exact p)) fun t ⟨ht, F, Vt, Kt, _⟩ => ?_
  rw [V.mem, m] at F Vt
  rw [V.gpr] at Vt
  exact ⟨ht, F, Vt, ((K.mono (by decide)).trans (V.keeps.mono (by decide))).trans (Kt.mono (by decide))⟩

theorem orOne_ok {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) :
    WP isa (.block (orOne L j)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = 2 * (num s.mem B (kw len) j / 2) + 1 ∧ Keeps [.eax, .ecx, .edx] s t := by
  have positive := h.kw_pos
  unfold orOne
  refine lowPtr_ok h hj fun u hu K m p => wp_movS (lowSrc hu hj p) fun v V _ => wp_orS rfl fun x X => ?_
  have KX : Keeps [.ecx] u x := V.keeps.trans X.keeps
  have hx := hu.keep KX (by decide) (by decide) (by rw [X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeLow_ok hx hj (by rw [PtrAt, KX.1 _ (by decide)]; exact p)) fun t ⟨ht, F, Vt, Kt, _⟩ => ?_
  have mx : x.mem = s.mem := by rw [X.mem, V.mem, m]
  rw [mx] at F Vt
  refine ⟨ht, F, ?_, ((K.mono (by decide)).trans (KX.mono (by decide))).trans (Kt.mono (by decide))⟩
  rw [Vt, X.gpr, V.gpr, m, bv_or_one]
  have low := low_word (B := B) (m := s.mem) (j := j) positive
  omega_using [low]

theorem clrLow_ok {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) :
    WP isa (.block (clrLow L j)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      num t.mem B (kw len) j = 2 * (num s.mem B (kw len) j / 2) ∧ Keeps [.eax, .ecx, .edx] s t ∧
      w32 t.mem B (arr (kw len) j + 4 * kw len) = w32 s.mem B (arr (kw len) j + 4 * kw len) := by
  have positive := h.kw_pos
  unfold clrLow
  refine lowPtr_ok h hj fun u hu K m p => wp_movS (lowSrc hu hj p) fun v V _ => wp_orS rfl fun x X => ?_
  refine wp_logicS (.inr rfl) rfl fun z Zr => ?_
  have KZ : Keeps [.ecx] u z := (V.keeps.trans X.keeps).trans Zr.keeps
  have hz := hu.keep KZ (by decide) (by decide) (by rw [Zr.mem, X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeLow_ok hz hj (by rw [PtrAt, KZ.1 _ (by decide)]; exact p)) fun t ⟨ht, F, Vt, Kt, top⟩ => ?_
  have mz : z.mem = s.mem := by rw [Zr.mem, X.mem, V.mem, m]
  rw [mz] at F Vt top
  refine ⟨ht, F, ?_, ((K.mono (by decide)).trans (KZ.mono (by decide))).trans (Kt.mono (by decide)), top⟩
  rw [Vt, Zr.gpr, ite_eq_right (by decide), X.gpr, V.gpr, m, bv_clr_one]
  have low := low_word (B := B) (m := s.mem) (j := j) positive
  omega_using [low]

theorem bitOf_ok {s : State} (h : RtWs L s B Z len N) {j sl : Nat} (hj : j < N)
    (hsl : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (.block (bitOf L sl j)) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [] [sl] s.mem t.mem ∧ slot t.mem B sl = num s.mem B (kw len) j % 2 ∧
      Keeps [.eax, .edx] s t := by
  have head := h.ws.hdr_le
  have positive := h.kw_pos
  unfold bitOf
  refine lowPtr_ok h hj fun u hu K m p => wp_movS (lowSrc hu hj p) fun v V _ => wp_logicS (.inl rfl) rfl fun x X => ?_
  have KX : Keeps [.eax] u x := V.keeps.trans X.keeps
  have hx := hu.ws.workspace.of_keeps KX (by decide)
  refine wp_storeS (hx.ea (by omega_using [hsl, head])) (hx.write (by omega_using [hsl, head])) fun t T => WP.block_nil ?_
  have r : Keeps [.eax, .edx] s t := ((K.mono (by decide)).trans (KX.mono (by decide))).trans (T.keeps [] |>.mono (by decide))
  have mem : t.mem = s.mem.writeW (off B sl) (x.gpr .eax) := by rw [T.mem, X.mem, V.mem, m]
  have out : Outside B sl 4 s.mem t.mem := by
    rw [mem]; exact writeW32_outside _ _ _ (by unfold VG.Impl.Rsa.X86.Keys.hdr at hsl; omega_using [hsl])
  refine ⟨h.keep r (by decide) (by decide) (out.mono (Nat.zero_le _) (by omega_using [hsl, head])), ?_, ?_, r⟩
  · exact Keep.of_slot out (by simp)
  · unfold slot
    rw [mem, w32_write_self, X.gpr, ite_eq_left rfl, V.gpr, m, bv_and_one,
      VG.Proof.Rsa.X86.Keys.num_mod2 _ _ positive]

end VG.Proof.Rsa.X86.KeyRt

end

end

/-! ### `Rsa.X86.KeyRt.Ops`, which this module and modules that import it used -/

section

/-! # The key workspace's operations at a run-time width: differences and selections

`sub3_ok`, `copy_ok` and `sel_ok` state what `Keys`' per-width lemmas do, for
the run-time width's code, on `RtWs`: a difference with its borrow in `ebx`,
and selections of whole arrays (`selectIn_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S arr_mono arr_end arr_disj)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem kk_false (len : Nat) : kk len false = kw len := rfl

/-- `[o] = [a] - [b]`, `w` words, and `ebx` the borrow. -/
theorem sub3_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (ho : o < N) (ha : a < N) (hb : b < N) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.sub3 L o a b) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o + num s.mem B (kw len) b =
        num s.mem B (kw len) a + 2 ^ (32 * kw len) * (t.gpr .ebx).toNat ∧
      (t.gpr .ebx).toNat ≤ 1 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.KeyRt.sub3
  refine WP.seq (WP.mono (chainSub_ok h ho ha hb false) fun u ⟨F, Kp, ⟨c, carry, value⟩, Ku⟩ => ?_)
  refine wp_movS rfl fun v V _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  obtain r : Keeps [.ebx] u t := V.keeps.trans T.keeps
  obtain mem : t.mem = u.mem := T.mem.trans V.mem
  obtain bit : (t.gpr .ebx).toNat = c.toNat := by
    rw [T.gpr, V.gpr, carry, ite_eq_left rfl]
    cases c <;> rfl
  refine ⟨F.keep r (by decide) (by decide) (by rw [mem]; exact Outside.refl _ _ _ _), by rw [mem]; exact Kp, ?_, ?_,
    Ku.trans (r.mono (by decide))⟩
  · rw [num, num, num, mem, bit]; exact value
  · rw [bit]; cases c <;> decide

/-- `[o] = [a]` where the mask `ecx` is all ones, else kept: `K` words, `o ≠ a`. -/
theorem selectIn_ok {s : State} (h : RtWs L s B Z len N) {o a : Nat} (ho : o < N) (ha : a < N) (hoa : o ≠ a)
    (extra : Bool) {k : Bool} (hk : s.gpr .ecx = cmask k) :
    WP isa (selectIn L o a extra) s fun t =>
      RtWs L t B Z len N ∧ Outside B (arr (kw len) o) (4 * kk len extra) s.mem t.mem ∧
      val32 t.mem B (arr (kw len) o) (kk len extra) =
        (if k then val32 s.mem B (arr (kw len) a) (kk len extra) else val32 s.mem B (arr (kw len) o) (kk len extra)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.ws.workspace.nowrap
  obtain fa := h.ws.arr_fit ha
  obtain fo := h.ws.arr_fit ho
  obtain sep := arr_disj (w := kw len) hoa
  obtain hK : 4 * kk len extra ≤ 4 * (kw len + 2) := by
    have := Bool.toNat_le extra; simp only [kk]; omega_arith
  simp only [S] at fa fo sep
  obtain hl := lenSrc h
  have hle := h.lenLe
  unfold selectIn
  rw [show count L .edi extra = count L .edi extra ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (arrPtr_ok hl hle h.edi (by decide) (by decide) (by omega_arith) fun u₁ K₁ m₁ p₁ _ => ?_)
  obtain hl₁ := hl.keep K₁ (by decide) m₁
  obtain edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok hl₁ hle edi₁ (by decide) (by decide) (by omega_arith) fun u₂ K₂ m₂ p₂ _ => ?_
  obtain hl₂ := hl₁.keep K₂ (by decide) m₂
  refine count_ok hl₂ hle fun u K₃ m₃ c₃ => WP.block_nil ?_
  obtain K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
  obtain m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  obtain ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (selectLoopX_ok (h.rt.of_keeps K) (x := arr (kw len) a) (d := arr (kw len) o)
    (N := kk len extra) k (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂) c₃ ecx) fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  obtain KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  obtain O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega_arith)
  unfold restoreEdi
  refine wp_movS (h.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h).symm)
  exact ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O0), by rw [U.mem]; exact O,
    by rw [U.mem]; exact V, K'⟩

/-- `[o] = [a]`, `w` words. -/
theorem copy_ok {s : State} (h : RtWs L s B Z len N) {o a : Nat} (ho : o < N) (ha : a < N) (hoa : o ≠ a) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.copy L o a) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = num s.mem B (kw len) a ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      w32 t.mem B (arr (kw len) o + 4 * kw len) =
        w32 s.mem B (arr (kw len) o + 4 * kw len) := by
  obtain fo := h.ws.arr_fit ho
  simp only [S] at fo
  unfold VG.Impl.Rsa.X86.KeyRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  obtain hu := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (selectIn_ok hu ho ha hoa false (k := true) U.gpr) fun t ⟨F, O, V, K⟩ => ?_
  rw [U.mem] at O V
  refine ⟨F, Keep.of_arr (d := 0) (by simpa using O) (by simp only [S, kk_false]; omega_arith) (by simp), ?_,
    (U.keeps.mono (by decide)).trans (K.mono (by decide)), ?_⟩
  · simp only [num, ite_true, kk_false] at V ⊢; exact V
  · exact O.w32 (by simp only [kk_false]; omega_arith) (by have := h.ws.workspace.nowrap; omega_arith)

open VG.Proof.Rsa.X86.Keys (slot) in
/-- The mask of a header word zero or one: all ones where it is one. -/
theorem mask_slot {s : State} (h : RtWs L s B Z len N) {sl : Nat} (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (bit : slot s.mem B sl ≤ 1) :
    readSrc s (.mem (sc sl)) = some (BitVec.ofNat 32 (slot s.mem B sl)) ∧
      (0 - BitVec.ofNat 32 (slot s.mem B sl) = cmask (decide (slot s.mem B sl ≠ 0))) ∧
      (BitVec.ofNat 32 (slot s.mem B sl) - 1 = cmask (decide (slot s.mem B sl = 0))) := by
  have := h.ws.hdr_le
  refine ⟨by rw [readSrc_sc h.ws.workspace (by omega_arith)]; simp [slot, w32], ?_⟩
  rcases (show slot s.mem B sl = 0 ∨ slot s.mem B sl = 1 by omega_arith) with e | e <;> rw [e] <;> decide

open VG.Proof.Rsa.X86.Keys (slot) in
/-- `[o]` set to `[b]` where the header word `sl` is one, else kept. -/
theorem maskSel_ok {s : State} (h : RtWs L s B Z len N) {o b sl : Nat} (ho : o < N) (hb : b < N) (hob : o ≠ b)
    (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (.seq (.block [.mov .ecx (.imm 0), .alu .sub .ecx (.mem (sc sl))]) (selectIn L o b false)) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = (if slot s.mem B sl = 0 then num s.mem B (kw len) o else num s.mem B (kw len) b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  obtain fo := h.ws.arr_fit ho
  simp only [S] at fo
  obtain ⟨rd, m0, _⟩ := mask_slot h hs bit
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  obtain rd' : readSrc u (.mem (sc sl)) = some (BitVec.ofNat 32 (slot s.mem B sl)) := by
    rw [← rd]; exact src_keep' U.keeps U.mem
  refine wp_subS rd' fun v V _ => WP.block_nil ?_
  obtain K : Keeps [.ecx] s v := U.keeps.trans V.keeps
  obtain mv : v.mem = s.mem := V.mem.trans U.mem
  obtain hv := h.keep K (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  obtain mask : v.gpr .ecx = cmask (decide (slot s.mem B sl ≠ 0)) := by rw [V.gpr, U.gpr]; exact m0
  refine WP.mono (selectIn_ok hv ho hb hob false mask) fun t ⟨F, O, V', Kt⟩ => ?_
  rw [mv] at O V'
  refine ⟨F, Keep.of_arr (d := 0) (by simpa using O) (by simp only [S, kk_false]; omega_arith) (by simp), ?_,
    (K.mono (by decide)).trans (Kt.mono (by decide))⟩
  simp only [num, kk_false] at V' ⊢
  rw [V']
  by_cases e : slot s.mem B sl = 0 <;> simp [e]

/-- `[o] = [b]` where the mask `ecx` is all ones, else `[a]`: `w` words, `o` apart from `a` and `b`. -/
theorem select3_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (ho : o < N) (ha : a < N) (hb : b < N)
    (hoa : o ≠ a) (hob : o ≠ b) {k : Bool} (hk : s.gpr .ecx = cmask k) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.select3 L o a b) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = (if k then num s.mem B (kw len) b else num s.mem B (kw len) a) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.ws.workspace.nowrap
  obtain fa := h.ws.arr_fit ha
  obtain fb := h.ws.arr_fit hb
  obtain fo := h.ws.arr_fit ho
  obtain sa := arr_disj (w := kw len) hoa
  obtain sb := arr_disj (w := kw len) hob
  have wpos := h.kw_pos
  simp only [S] at fa fb fo sa sb
  obtain hl := lenSrc h
  have hle := h.lenLe
  unfold VG.Impl.Rsa.X86.KeyRt.select3
  rw [show count L .edx false = count L .edx false ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (arrPtr_ok hl hle h.edi (by decide) (by decide) (by omega_arith) fun u₁ K₁ m₁ p₁ _ => ?_)
  obtain hl₁ := hl.keep K₁ (by decide) m₁
  obtain edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok hl₁ hle edi₁ (by decide) (by decide) (by omega_arith) fun u₂ K₂ m₂ p₂ _ => ?_
  obtain hl₂ := hl₁.keep K₂ (by decide) m₂
  obtain edi₂ : (u₂.gpr .edi).toNat = B.toNat := by rw [K₂.1 _ (by decide)]; exact edi₁
  refine arrPtr_ok hl₂ hle edi₂ (by decide) (by decide) (by omega_arith) fun u₃ K₃ m₃ p₃ _ => ?_
  obtain hl₃ := hl₂.keep K₃ (by decide) m₃
  refine count_ok hl₃ hle fun u K₄ m₄ c₄ => WP.block_nil ?_
  obtain K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  obtain m : u.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (select3LoopX_ok (h.rt.of_keeps K) (x := arr (kw len) a) (y := arr (kw len) b)
    (d := arr (kw len) o) (N := kw len) k wpos (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂)
    (by rw [PtrAt, K₄.1 _ (by decide)]; exact p₃) (by rw [c₄]; simp) ecx) fun t ⟨O, V, Kt⟩ => ?_)
  rw [m] at O V
  obtain KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  obtain O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega_arith)
  unfold restoreEdi
  refine wp_movS (h.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h).symm)
  refine ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O0),
    Keep.of_arr (d := 0) (by rw [U.mem]; simpa using O) (by simp only [S]; omega_arith) (by simp), ?_,
    K'.mono (by decide)⟩
  rw [num, U.mem, V]

open VG.Proof.Rsa.X86.Keys (slot) in
/-- `[o] = [b]` if the header word `sl` is one, else `[a]`, for `o` apart from `a` or `b`. -/
theorem sel_ok {s : State} (h : RtWs L s B Z len N) {o a b sl : Nat} (ho : o < N) (ha : a < N) (hb : b < N)
    (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (bit : slot s.mem B sl ≤ 1) (hab : o ≠ a ∨ o ≠ b) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.sel L o a b sl) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = (if slot s.mem B sl = 0 then num s.mem B (kw len) a else num s.mem B (kw len) b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  obtain fo := h.ws.arr_fit ho
  simp only [S] at fo
  unfold VG.Impl.Rsa.X86.KeyRt.sel
  by_cases hob : o = b
  · subst hob
    obtain hoa : o ≠ a := hab.resolve_right (fun e => e rfl)
    rw [ite_eq_left rfl]
    obtain ⟨rd, _, m1⟩ := mask_slot h hs bit
    refine WP.seq (wp_movS rd fun u U _ => wp_subS rfl fun v V _ => WP.block_nil ?_)
    obtain K : Keeps [.ecx] s v := U.keeps.trans V.keeps
    obtain mv : v.mem = s.mem := V.mem.trans U.mem
    obtain hv := h.keep K (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
    obtain mask : v.gpr .ecx = cmask (decide (slot s.mem B sl = 0)) := by rw [V.gpr, U.gpr]; exact m1
    refine WP.mono (selectIn_ok hv ho ha hoa false mask) fun t ⟨F, O, V', Kt⟩ => ?_
    rw [mv] at O V'
    refine ⟨F, Keep.of_arr (d := 0) (by simpa using O) (by simp only [S, kk_false]; omega_arith) (by simp), ?_,
      (K.mono (by decide)).trans (Kt.mono (by decide))⟩
    simp only [num, kk_false] at V' ⊢
    rw [V']
    by_cases e : slot s.mem B sl = 0 <;> simp [e]
  · rw [ite_eq_right hob]
    by_cases hoa : o = a
    · subst hoa
      rw [ite_eq_left rfl]
      exact maskSel_ok h ho hb hob hs bit
    · rw [ite_eq_right hoa]
      obtain ⟨rd, m0, _⟩ := mask_slot h hs bit
      refine WP.seq (wp_movS rfl fun u U _ => ?_)
      obtain rd' : readSrc u (.mem (sc sl)) = some (BitVec.ofNat 32 (slot s.mem B sl)) := by
        rw [← rd]; exact src_keep' U.keeps U.mem
      refine wp_subS rd' fun v V _ => WP.block_nil ?_
      obtain K : Keeps [.ecx] s v := U.keeps.trans V.keeps
      obtain mv : v.mem = s.mem := V.mem.trans U.mem
      obtain hv := h.keep K (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
      obtain mask : v.gpr .ecx = cmask (decide (slot s.mem B sl ≠ 0)) := by rw [V.gpr, U.gpr]; exact m0
      refine WP.mono (select3_ok hv ho ha hb hoa hob mask) fun t ⟨F, Kp, V', Kt⟩ => ?_
      rw [mv] at Kp V'
      refine ⟨F, Kp, ?_, (K.mono (by decide)).trans Kt⟩
      rw [V']
      by_cases e : slot s.mem B sl = 0 <;> simp [e]

end VG.Proof.Rsa.X86.KeyRt

end

end

/-! # The key workspace's header words at a run-time width

What leaves `edi` and the stack and writes inside the workspace keeps the
arguments (`RtWs.lift`), so `Keys`' lemmas about header words hold on `RtWs`
(`storeSlot_ok`, `andS_ok`); and, through `Ops`, the equality test (`eqS_ok`)
and a header word added to an array's low word (`addLow_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot)
open VG.Proof.Rsa.KeyBits32

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- A frame inside the workspace keeps everything else. -/
theorem keep_outside {s : State} (h : Ws s B Z (kw len) N) {js ds : List Nat} {m m' : Mem}
    (F : Keep B (kw len) js ds m m') (hj : ∀ j ∈ js, j < N) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    Outside B 0 Z m m' := by
  have head := h.hdr_le
  refine outs_outside F fun r hr => ?_
  simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj', rfl⟩ | ⟨d, hd', rfl⟩
  · exact h.arr_fit (hj j hj')
  · have := hd d hd'; dsimp only; omega_using [head, this]

/-- A `Keys` lemma on `RtWs`: what keeps `edi` and `esp` and writes in the workspace. -/
theorem RtWs.lift {s : State} (h : RtWs L s B Z len N) {p : Prog isa} {rs : List Reg} {js ds : List Nat}
    {P : State → Prop} (esp : .esp ∉ rs) (hj : ∀ j ∈ js, j < N)
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (k : WP isa p s fun t => Ws t B Z (kw len) N ∧ Keep B (kw len) js ds s.mem t.mem ∧ P t ∧ Keeps rs s t) :
    WP isa p s fun t => RtWs L t B Z len N ∧ Keep B (kw len) js ds s.mem t.mem ∧ P t ∧ Keeps rs s t :=
  WP.mono k fun _ ⟨W, F, p, K⟩ =>
    ⟨⟨W, h.lenArg.imp fun _ ⟨l, e, c⟩ => ⟨l, e, c.keep K esp (keep_outside W F hj hd)⟩, h.wsArg.keep K esp (keep_outside W F hj hd), h.lenLe,
      h.layLen⟩, F, p, K⟩

theorem storeSlot_ok {s : State} (h : RtWs L s B Z len N) {d : Nat} (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [] [d] s.mem t.mem ∧
      slot t.mem B d = (s.gpr r).toNat ∧ Keeps [] s t :=
  h.lift (by decide) (by simp) (by simpa using hd) (VG.Proof.Rsa.X86.Keys.store_slot h.ws hd r)

theorem andS_ok {s : State} (h : RtWs L s B Z len N) {d a b : Nat} (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (ha : a + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (hb : b + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (ba : slot s.mem B a ≤ 1) (bb : slot s.mem B b ≤ 1) :
    WP isa (.block (VG.Impl.Rsa.X86.Keys.andS d a b)) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [] [d] s.mem t.mem ∧
      slot t.mem B d = (if slot s.mem B a = 1 ∧ slot s.mem B b = 1 then 1 else 0) ∧ Keeps [.eax] s t :=
  h.lift (by decide) (by simp) (by simpa using hd) (VG.Proof.Rsa.X86.Keys.andS_ok h.ws hd ha hb ba bb)

theorem eqS_ok {s : State} (h : RtWs L s B Z len N) {d a b t : Nat}
    (ht : t < N) (ha : a < N) (hb : b < N) (hta : t ≠ a) (htb : t ≠ b) (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.eqS L d a b t) s fun u => RtWs L u B Z len N ∧
      Keep B (kw len) [t] [VG.Impl.Rsa.X86.Keys.sT, d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B (kw len) a = num s.mem B (kw len) b then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s u := by
  have hT : VG.Impl.Rsa.X86.Keys.sT + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  unfold VG.Impl.Rsa.X86.KeyRt.eqS
  refine WP.seq (WP.mono (sub3_ok h ht ha hb) fun u1 ⟨h1, k1, v1, b1, r1⟩ => ?_)
  refine WP.seq (WP.mono (storeSlot_ok h1 hT .ebx) fun u2 ⟨h2, k2, s2, r2⟩ => ?_)
  refine WP.seq (WP.mono (sub3_ok h2 ht hb ha) fun u3 ⟨h3, k3, v3, b3, r3⟩ => ?_)
  have head := h3.ws.hdr_le
  refine wp_orS (readSrc_sc h3.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.sT VG.Impl.Rsa.X86.Keys.hdr at *; omega_using [head]))
    fun s5 u5 => ?_
  refine wp_logicS (.inr rfl) rfl fun s6 u6 => ?_
  have h6 := h3.keep (u5.keeps.trans u6.keeps) (by decide) (by decide)
    (by rw [u6.mem, u5.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok h6 hd .ebx) fun u ⟨h7, k7, e7, r7⟩ => ?_
  have mem : s6.mem = u3.mem := u6.mem.trans u5.mem
  rw [mem] at k7
  have fa := h.ws.fit64 ha
  have fb := h.ws.fit64 hb
  have na2 : num u2.mem B (kw len) a = num s.mem B (kw len) a := by
    rw [k2.num (by simp) (by simp; decide) fa, k1.num (by simpa using hta) (by simp) fa]
  have nb2 : num u2.mem B (kw len) b = num s.mem B (kw len) b := by
    rw [k2.num (by simp) (by simp; decide) fb, k1.num (by simpa using htb) (by simp) fb]
  rw [na2, nb2] at v3
  have sT3 : slot u3.mem B VG.Impl.Rsa.X86.Keys.sT = (u1.gpr .ebx).toNat := by rw [k3.slot hT (by simp), s2]
  refine ⟨h7, (k1.join k2 (js := [t]) (ds := [VG.Impl.Rsa.X86.Keys.sT, d])).join
    (k3.join k7 (js := [t]) (ds := [VG.Impl.Rsa.X86.Keys.sT, d])) (js := [t]) (ds := [VG.Impl.Rsa.X86.Keys.sT, d]),
    ?_, ?_⟩
  · rw [e7, u6.gpr, ite_eq_right (by decide), u5.gpr]
    have e : (u3.mem.readW (off B VG.Impl.Rsa.X86.Keys.sT) 32).toNat = (u1.gpr .ebx).toNat := sT3
    rw [bv_nor_bits b3 (by rw [e]; exact b1), e]
    have p1 := VG.Proof.Rsa.borrow_iff v1 (val32_lt _ _ _ _) b1
    have p3 := VG.Proof.Rsa.borrow_iff v3 (val32_lt _ _ _ _) b3
    by_cases eq : num s.mem B (kw len) a = num s.mem B (kw len) b
    · have c1 := p1.mpr (by omega_using [eq])
      have c3 := p3.mpr (by omega_using [eq])
      simp [c1, c3, eq]
    · have c : ¬((u3.gpr .ebx).toNat = 0 ∧ (u1.gpr .ebx).toNat = 0) :=
        fun hh => eq (by have := p1.mp hh.2; have := p3.mp hh.1; omega_arith)
      simp only [c, eq, ↓reduceIte]
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u5.keeps.mono (by decide)).trans ((u6.keeps.mono (by decide)).trans (r7.mono (by decide))))))

/-- `[j]`'s low word plus the header word `sl`, for `[j]` even and the word a bit. -/
theorem addLow_ok {s : State} (h : RtWs L s B Z len N) {j sl : Nat} (hj : j < N)
    (hsl : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (.block (addLow L j sl)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [j] [] s.mem t.mem ∧
      (num s.mem B (kw len) j % 2 = 0 → slot s.mem B sl ≤ 1 →
        num t.mem B (kw len) j = num s.mem B (kw len) j + slot s.mem B sl) ∧ Keeps [.eax, .ecx, .edx] s t ∧
      w32 t.mem B (arr (kw len) j + 4 * kw len) = w32 s.mem B (arr (kw len) j + 4 * kw len) := by
  have positive := h.kw_pos
  have head := h.ws.hdr_le
  unfold addLow
  refine lowPtr_ok h hj fun u hu K m p => wp_movS (lowSrc hu hj p) fun v V _ => ?_
  have hv := hu.keep V.keeps (by decide) (by decide) (by rw [V.mem]; exact Outside.refl _ _ _ _)
  refine wp_addS (readSrc_sc hv.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at hsl head; omega_using [hsl, head])) fun x X _ => ?_
  have KX : Keeps [.ecx] u x := V.keeps.trans X.keeps
  have hx := hu.keep KX (by decide) (by decide) (by rw [X.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeLow_ok hx hj (by rw [PtrAt, KX.1 _ (by decide)]; exact p)) fun t ⟨ht, F, Vt, Kt, top⟩ => ?_
  have mx : x.mem = s.mem := by rw [X.mem, V.mem, m]
  rw [mx] at F Vt top
  refine ⟨ht, F, ?_, ((K.mono (by decide)).trans (KX.mono (by decide))).trans (Kt.mono (by decide)), top⟩
  intro even bit
  have low := low_word (B := B) (m := s.mem) (j := j) positive
  have sv : (v.mem.readW (off B sl) 32).toNat = slot s.mem B sl := by rw [V.mem, m]
  rw [Vt, X.gpr, V.gpr, m, BitVec.toNat_add, sv, ← low]
  have lowEven : num s.mem B (kw len) j % 2 ^ 32 % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide)]; exact even
  have lt : num s.mem B (kw len) j % 2 ^ 32 + slot s.mem B sl < 2 ^ 32 := by
    have := Nat.mod_lt (num s.mem B (kw len) j) (show 0 < 2 ^ 32 by decide)
    omega_using [even, bit]
  rw [Nat.mod_eq_of_lt lt]
  omega_using []

end VG.Proof.Rsa.X86.KeyRt
