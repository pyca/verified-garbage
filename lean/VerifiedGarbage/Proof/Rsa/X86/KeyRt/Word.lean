module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.Framework.Omega

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
  refine wp_storeS (ea_ptr h.rt p (d := 0) (by omega)) (ws_write h.rt (y := arr (kw len) j + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  rw [Nat.add_zero] at T
  have outside := writeW32_outside s.mem B (d := arr (kw len) j) (s.gpr .ecx) (by omega)
  refine ⟨h.keep (T.keeps []) (by decide) (by decide) (by rw [T.mem]; exact outside.mono (Nat.zero_le _) (by omega)),
    ?_, ?_, T.keeps [], ?_⟩
  · rw [T.mem]
    exact Keep.of_arr (d := 0) (by simpa using outside) (by unfold S; omega) (by simp)
  · rw [T.mem]
    exact VG.Proof.Rsa.KeyWorkspace.num_write0 _ _ positive (by change arr (kw len) j + 4 * kw len ≤ 2 ^ 64; omega) _
  · rw [T.mem]; exact outside.w32 (by omega) (by omega)

/-- The array's low word, through `eax`. -/
theorem lowSrc {s : State} (h : RtWs L s B Z len N) {j : Nat} (hj : j < N) (p : PtrAt s B .eax (arr (kw len) j)) :
    readSrc s (.mem (at_ .eax 0)) = some (s.mem.readW (off B (arr (kw len) j)) 32) := by
  have fit := h.ws.arr_fit hj
  simp only [S] at fit
  rw [readSrc_ptr h.rt p (d := 0) (by omega), Nat.add_zero]

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
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (by decide) (by decide) (by omega) fun u K m p _ => ?_
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
  omega

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
  omega

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
  refine wp_storeS (hx.ea (by omega)) (hx.write (by omega)) fun t T => WP.block_nil ?_
  have r : Keeps [.eax, .edx] s t := ((K.mono (by decide)).trans (KX.mono (by decide))).trans (T.keeps [] |>.mono (by decide))
  have mem : t.mem = s.mem.writeW (off B sl) (x.gpr .eax) := by rw [T.mem, X.mem, V.mem, m]
  have out : Outside B sl 4 s.mem t.mem := by
    rw [mem]; exact writeW32_outside _ _ _ (by unfold VG.Impl.Rsa.X86.Keys.hdr at hsl; omega)
  refine ⟨h.keep r (by decide) (by decide) (out.mono (Nat.zero_le _) (by omega)), ?_, ?_, r⟩
  · exact Keep.of_slot out (by simp)
  · unfold slot
    rw [mem, w32_write_self, X.gpr, ite_eq_left rfl, V.gpr, m, bv_and_one,
      VG.Proof.Rsa.X86.Keys.num_mod2 _ _ positive]

end VG.Proof.Rsa.X86.KeyRt
