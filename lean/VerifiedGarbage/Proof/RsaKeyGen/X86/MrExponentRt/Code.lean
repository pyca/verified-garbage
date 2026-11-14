module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentReady
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Scan
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassWord
import VerifiedGarbage.Proof.Mont.Halve32
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairTwos
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentMarker
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `RsaKeyGen.X86.MrExponentRt.Half`, which only this module used -/

section

/-! # Array 27 halved in place at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MrExponentRt

/-- A pointer into the working space, from `edi` at its base. -/
theorem ptr_edi {t : State} {W : Addr} {L x : Nat} (S : Scr t W L) {r : Reg} (P : PtrAt t W r x) (_fit : x < L) :
    t.gpr r = t.gpr .edi + BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have nowrap := S.nowrap
  rw [P, BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
  omega_using []

/-- One word of an in-place pass, at `ebp`, and `esi` down one. -/
theorem halfStep_ok {t : State} {W : Addr} {L x : Nat} (S : Scr t W L) (bp : PtrAt t W .ebp x)
    (aligned : x % 4 = 0) (fit : x + 8 ≤ L) {choice : Bool} (mask : t.gpr .ecx = cmask choice) :
    WP isa (.block halfStep) t fun u =>
      Outside W x 4 t.mem u.mem ∧
      w32 u.mem W x = (if choice then w32 t.mem W x / 2 + 2 ^ 31 * (w32 t.mem W (x + 4) % 2) else w32 t.mem W x) ∧
      PtrAt u W .ebp (x + 4) ∧ u.gpr .esi = t.gpr .esi - 1 ∧ u.zf = some (t.gpr .esi - 1 == 0) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] t u := by
  have index : 0 + 4 * (x / 4) = x := by omega_using [aligned]
  have pointer : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (x / 4)) := by
    rw [ptr_edi S bp (by omega_using [fit])]; congr 2; omega_using [aligned]
  unfold halfStep
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.HalfPass.step_ok (src := 0) (out := 0) S pointer
    (by omega_using [fit]) (by omega_using [fit]) mask) fun a ⟨O, V, K⟩ => ?_)
  refine wp_addS rfl fun b B _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  rw [index] at O V
  have esiB : b.gpr .esi = t.gpr .esi := by rw [B.other .esi (by decide), K.1 .esi (by decide)]
  refine ⟨by rw [U.mem, B.mem]; exact O, by rw [U.mem, B.mem, V],
    ?_, by rw [U.gpr, esiB], by rw [Z, esiB], ((K.mono (by decide)).widen B.keeps).widen U.keeps⟩
  rw [PtrAt, U.other .ebp (by decide), B.gpr, K.1 .ebp (by decide), ptr_add bp]
  rfl

theorem halfLoop_ok {t₀ : State} {W : Addr} {L x N : Nat} (S : Scr t₀ W L) (positive : 0 < N)
    (aligned : x % 4 = 0) (fit : x + 4 * (N + 1) ≤ L) (top : w32 t₀.mem W (x + 4 * N) = 0)
    (bp : PtrAt t₀ W .ebp x) (count : (t₀.gpr .esi).toNat = N) {choice : Bool} (mask : t₀.gpr .ecx = cmask choice) :
    WP isa (.loop (.block halfStep) .ne) t₀ fun u =>
      Outside W x (4 * N) t₀.mem u.mem ∧
      val32 u.mem W x N = (if choice then val32 t₀.mem W x N / 2 else val32 t₀.mem W x N) ∧
      PtrAt u W .ebp (x + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] t₀ u := by
  have nowrap := S.nowrap
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop positive (fun j t =>
      Keeps [.eax, .ebx, .edx, .ebp, .esi] t₀ t ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      (∀ i < j, w32 t.mem W (x + 4 * i) =
        if choice then w32 t₀.mem W (x + 4 * i) / 2 + 2 ^ 31 * (w32 t₀.mem W (x + 4 * i + 4) % 2)
        else w32 t₀.mem W (x + 4 * i)) ∧
      PtrAt t W .ebp (x + 4 * j) ∧ (t.gpr .esi).toNat = N - j) ?_
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), by simpa using bp,
      by simpa using count⟩) ?_
  · rintro j t index ⟨K, O, V, P, esi⟩
    have St := S.of_keeps K (by decide)
    refine WP.mono (halfStep_ok (choice := choice) St P (by omega_using [aligned]) (by omega_using [fit, index]) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Pu, esiU, Z, Ku⟩ => ?_
    obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf esi index
    have sameLo : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) := O.w32 (by omega_using []) (by omega_using [fit, nowrap, index])
    have sameHi : w32 t.mem W (x + 4 * j + 4) = w32 t₀.mem W (x + 4 * j + 4) := O.w32 (by omega_using []) (by omega_using [fit, nowrap, index])
    refine ⟨⟨K.trans Ku, (O.mono (by omega_using []) (by omega_using [])).trans (Ou.mono (by omega_using []) (by omega_using [])), ?_,
      by rw [show x + 4 * (j + 1) = x + 4 * j + 4 by omega_using []]; exact Pu, by rw [esiU]; exact next⟩,
      by rw [Z, last]⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega_using [before]) (by omega_using [fit, nowrap, index, hi])]
      exact V i before
    · rw [value, sameLo, sameHi]
  · rintro u ⟨K, O, V, P, _⟩
    refine ⟨O, ?_, P, K⟩
    cases choice
    · exact val32_congr_at t₀.mem u.mem W N x x V
    · apply val32_halve_at t₀.mem u.mem W N x x
      intro i hi
      rw [V i hi, show x + 4 * i + 4 = x + 4 * (i + 1) by omega_using []]
      by_cases last : i + 1 = N
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

/-- `half`: array 27 halved in place where the mask `ecx` is all ones. -/
theorem half_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) (S : Scr s g.W g.L)
    (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0) {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa half s fun t =>
      Outside g.W (g.array 27) (4 * g.words) s.mem t.mem ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if choice then val32 s.mem g.W (g.array 27) g.words / 2 else val32 s.mem g.W (g.array 27) g.words) ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  have fit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have positive := v.minWidth
  unfold half
  refine WP.seq (WP.block_append (WP.mono (C.ptr v 27 (by decide) .ebp (by decide) (by decide))
    fun a ⟨P, Ma, Ka⟩ => ?_))
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.mono (words_ok v Ca) fun b ⟨count, Mb, Kb⟩ => ?_
  have K : Keeps [.edx, .ebp, .esi] s b := (Ka.mono (by decide)).widen Kb
  have Pb : PtrAt b g.W .ebp (g.array 27) := by rw [PtrAt, Kb.1 .ebp (by decide)]; exact P
  have M : b.mem = s.mem := Mb.trans Ma
  refine WP.mono (halfLoop_ok (choice := choice) (S.of_keeps K (by decide)) (by unfold Geometry.words; omega_using [positive])
    (by simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using [])
    (by unfold Geometry.words; omega_using [fit]) (by rw [M]; exact top) Pb count
    (by rw [K.1 .ecx (by decide)]; exact mask)) fun t ⟨O, V, Pt, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, V, Pt, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MrExponentRt

end

end


/-! # Miller–Rabin's exponent and marker, prepared at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MrExponentRt
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)
open VG.Proof.RsaKeyGen.X86.Exponent (preparedRanges ready_keep)

/-- The marker of `c − 1`: `2 ^ (v₂(c − 1) mod 64)`. -/
abbrev Marker (c : Nat) : BitVec 64 := BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)

theorem outs_prepared {g : Geometry} {d n : Nat} {m m' : Mem} (O : Outside g.W d n m m')
    (inside : ∃ R ∈ preparedRanges g, R.1 ≤ d ∧ d + n ≤ R.1 + R.2) : Outs g.W (preparedRanges g) m m' :=
  Outs.cover (Outs.of_outside O (List.mem_singleton_self _)) fun r mem => by
    obtain rfl := List.mem_singleton.mp mem
    exact inside

/-- A write within array 27, its top word or the marker above it. -/
theorem outs27 {g : Geometry} {d n : Nat} {m m' : Mem} (O : Outside g.W d n m m')
    (lo : g.array 27 ≤ d) (hi : d + n ≤ g.array 27 + 8 * g.w + 8) : Outs g.W (preparedRanges g) m m' := by
  refine outs_prepared O ⟨(g.array 27, 8 * g.w + 8), ?_, lo, by dsimp only; omega_using [hi]⟩
  simp only [preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false, or_true]

/-- The marker from the scanned pair, stored at header byte 136. -/
theorem markerStore_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (large : 1 < c)
    (selected : (s.gpr .esi ++ s.gpr .ebx).toNat =
      (c - 1) / 2 ^ (64 * ((Spec.Rsa.splitTwos (c - 1)).1 / 64)) % 2 ^ 64) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.LowBit.code ++ VG.Impl.RsaKeyGen.X86.Exponent.saveMarker)) s fun t =>
      Ready g c capacity p t ∧ word t.mem g.W 136 = Marker c ∧ Outside g.W 136 8 s.mem t.mem ∧
      Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps Exponent.clob s t := by
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentMarker.lowBit_marker (by omega_using [large]) selected)
    fun a ⟨value, Ma, Ka⟩ => ?_)
  have Ksa : Keeps Exponent.clob s a := Ka.mono (by decide)
  have Sa := S.scratch.of_keeps Ksa (by decide)
  have head := v.headerFit
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Header.storePair_ok Sa (offset := 136) (by omega_using [head]))
    fun t ⟨Mt, Ot, Kt⟩ => ?_
  have O : Outside g.W 136 8 s.mem t.mem := by rw [← Ma]; exact Ot
  have outs : Outs g.W (preparedRanges g) s.mem t.mem :=
    outs_prepared O ⟨(136, 8), by unfold preparedRanges Exponent.ranges; exact List.mem_cons_self,
      Nat.le_refl _, Nat.le_refl _⟩
  have K : Keeps Exponent.clob s t := Ksa.trans (Kt.mono (by decide))
  refine ⟨ready_keep v S outs K, ?_, O, outs, K⟩
  rw [VG.Proof.Mont.word, Mt, Mem.readW_writeW_self64, value]

theorem copyTops_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) :
    WP isa copyTops s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 27) g.words = val32 s.mem g.W (g.array 0) g.words ∧
      w32 t.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ t.gpr .ecx = cmask true ∧
      word t.mem g.W 136 = word s.mem g.W 136 ∧ Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps Exponent.clob s t := by
  have fit0 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 0) (by decide)
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have apart := VG.Proof.RsaKeyGen.X86.Prepared.paddedBefore g (i := 0) (j := 27) (by decide)
  have lo0 := v.arrayHeader 0
  have nowrap := S.scratch.nowrap
  have words : g.words = 2 * g.w := rfl
  unfold copyTops
  refine WP.seq (WP.mono (copy_ends v S.context 27 0 (by decide) (by decide)) fun a ⟨V, O, K, Ca, bp, bx⟩ => ?_)
  refine wp_movS rfl fun b B _ => ?_
  have hwb : Ws b g.W g.L := Ca.ws.of_keeps B.keeps
  have bxb : PtrAt b g.W .ebx (g.array 0 + 4 * g.words) := by rw [PtrAt, B.other .ebx (by decide)]; exact bx
  refine wp_storeS (ea_ptr hwb bxb (d := 0) (by omega_using [fit0, words]))
    (ws_write hwb (y := g.array 0 + 4 * g.words + 0) (n := 4) (by omega_using [fit0, words])) fun d D => ?_
  have hwd : Ws d g.W g.L := hwb.of_keeps (D.keeps [])
  have bpd : PtrAt d g.W .ebp (g.array 27 + 4 * g.words) := by
    rw [PtrAt, D.gpr, B.other .ebp (by decide)]; exact bp
  refine wp_storeS (ea_ptr hwd bpd (d := 0) (by omega_using [fit27, words]))
    (ws_write hwd (y := g.array 27 + 4 * g.words + 0) (n := 4) (by omega_using [fit27, words])) fun e E => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have eaxD : d.gpr .eax = 0#32 := by rw [D.gpr, B.gpr]; rfl
  have O1 : Outside g.W (g.array 0 + 4 * g.words) 4 a.mem d.mem := by
    rw [D.mem, B.mem, ← Nat.add_zero (g.array 0 + 4 * g.words)]
    exact writeW32_outside _ _ _ (by omega_using [fit0, nowrap, words])
  have O2 : Outside g.W (g.array 27 + 4 * g.words) 4 d.mem t.mem := by
    rw [T.mem, E.mem, ← Nat.add_zero (g.array 27 + 4 * g.words)]
    exact writeW32_outside _ _ _ (by omega_using [fit27, nowrap, words])
  have K' : Keeps Exponent.clob s t :=
    (((K.mono (by decide)).widen B.keeps).widen (D.keeps [])).trans ((E.keeps []).mono (by decide)) |>.widen T.keeps
  have Oall : Outs g.W (preparedRanges g) s.mem t.mem :=
    ((outs27 O (Nat.le_refl _) (by omega_using [words])).trans (outs_prepared O1
      ⟨(g.array 0 + 8 * g.w, 4), by
        unfold preparedRanges Exponent.ranges
        exact List.mem_cons_of_mem _ List.mem_cons_self, by omega_using [words], by omega_using [words]⟩)).trans
      (outs27 O2 (by omega_using []) (by omega_using [words]))
  refine ⟨ready_keep v S Oall K', ?_, ?_, by rw [T.gpr]; rfl, ?_, Oall, K'⟩
  · rw [O2.val32 (Or.inl (by omega_using [])) (by omega_using [fit27, nowrap, words]), O1.val32 (Or.inr (by omega_using [apart, words])) (by omega_using [fit27, nowrap, words])]
    exact V
  · rw [T.mem, E.mem, Nat.add_zero, w32_write_self, eaxD]
    rfl
  · rw [O2.word (Or.inl (by omega_using [apart, lo0])) (by omega_using []), O1.word (Or.inl (by omega_using [lo0])) (by omega_using []), O.word (Or.inl (by omega_using [apart, lo0])) (by omega_using [])]

theorem halfStage_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa half s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if choice then val32 s.mem g.W (g.array 27) g.words / 2 else val32 s.mem g.W (g.array 27) g.words) ∧
      w32 t.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ word t.mem g.W 136 = word s.mem g.W 136 ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Outs g.W (preparedRanges g) s.mem t.mem ∧
      Keeps Exponent.clob s t := by
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have lo := v.arrayHeader 27
  have nowrap := S.scratch.nowrap
  have words : g.words = 2 * g.w := rfl
  refine WP.mono (half_ok v S.context S.scratch top mask) fun t ⟨O, V, P, K⟩ => ?_
  have K' : Keeps Exponent.clob s t := K.mono (by decide)
  have outs := outs27 O (Nat.le_refl _) (by omega_using [words])
  refine ⟨ready_keep v S outs K', V, ?_, ?_, P, outs, K'⟩
  · rw [O.w32 (Or.inr (Nat.le_refl _)) (by omega_using [fit27, nowrap, words])]; exact top
  · rw [O.word (Or.inl (by omega_using [lo])) (by omega_using [])]

theorem halfIf_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0) {j k : Nat}
    (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3) (value : word s.mem g.W 136 = BitVec.twoPow 64 k) :
    WP isa (halfIf j) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem g.W (g.array 27) g.words / 2
          else val32 s.mem g.W (g.array 27) g.words) ∧
      w32 t.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ word t.mem g.W 136 = BitVec.twoPow 64 k ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Outs g.W (preparedRanges g) s.mem t.mem ∧
      Keeps Exponent.clob s t := by
  have head := v.headerFit
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.SigMask.code_sig S.scratch
    (by unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [head]) index choice value)
    fun a ⟨mask, M, K⟩ => ?_)
  have Ka : Keeps Exponent.clob s a := K.mono (by decide)
  have Oa : Outs g.W (preparedRanges g) s.mem a.mem := by rw [M]; exact Outs.refl _ _ _
  refine WP.mono (halfStage_ok v (ready_keep v S Oa Ka) (by rw [M]; exact top) mask)
    fun t ⟨T, V, topT, markerT, P, O, Kt⟩ => ?_
  rw [M] at V markerT
  exact ⟨T, by simpa only [decide_eq_true_eq] using V, topT, markerT.trans value, P, Oa.trans O, Ka.trans Kt⟩

theorem finish_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    (bp : PtrAt s g.W .ebp (g.array 27 + 4 * g.words)) :
    WP isa (.block finish) s fun t =>
      word t.mem g.W (g.array 27 + 4 * g.words) = word s.mem g.W 136 ∧
      Outside g.W (g.array 27 + 4 * g.words) 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  have nowrap := S.nowrap
  have words : g.words = 2 * g.w := rfl
  have hw : Ws s g.W g.L := ⟨S.wr, S.nowrap⟩
  unfold finish
  refine wp_movS (readSrc_sc S (d := 136) (by omega_using [head])) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 140) (by omega_using [head])) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have hwb := hw.of_keeps K
  have bpb : PtrAt b g.W .ebp (g.array 27 + 4 * g.words) := by rw [PtrAt, K.1 .ebp (by decide)]; exact bp
  refine wp_storeS (ea_ptr hwb bpb (d := 0) (by omega_using [fit27, words]))
    (ws_write hwb (y := g.array 27 + 4 * g.words + 0) (n := 4) (by omega_using [fit27, words])) fun d D => ?_
  have hwd := hwb.of_keeps (D.keeps [])
  have bpd : PtrAt d g.W .ebp (g.array 27 + 4 * g.words) := by rw [PtrAt, D.gpr]; exact bpb
  refine wp_storeS (ea_ptr hwd bpd (d := 4) (by omega_using [fit27, words]))
    (ws_write hwd (y := g.array 27 + 4 * g.words + 4) (n := 4) (by omega_using [fit27, words])) fun t T => WP.block_nil ?_
  have memory : t.mem = (b.mem.writeW (off g.W (g.array 27 + 4 * g.words)) (b.gpr .eax)).writeW
      (off g.W (g.array 27 + 4 * g.words) + BitVec.ofNat 64 4) (b.gpr .edx) := by
    rw [T.mem, D.mem, D.gpr, Nat.add_zero]
    congr 1
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  have pair : b.gpr .edx ++ b.gpr .eax = word s.mem g.W 136 := by
    rw [B.gpr, B.other .eax (by decide), A.gpr, A.mem,
      VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  refine ⟨?_, ?_, K.widen ((D.keeps []).trans (T.keeps []))⟩
  · rw [VG.Proof.Mont.word, memory, ← VG.Proof.Rc2.Word32.write64_pair, Mem.readW_writeW_self64, pair]
  · rw [T.mem, D.mem, Mb]
    exact ((writeW32_outside _ _ _ (by omega_using [fit27, nowrap, words])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [fit27, nowrap, words])).mono (by omega_using []) (by omega_using []))

theorem prepared_fits {g : Geometry} (v : g.Valid) : ∀ r ∈ preparedRanges g, r.1 + r.2 ≤ g.L := by
  have srcFit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 0) (by decide)
  have outFit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  intro r mem
  simp only [preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith

theorem code_ok {g : Geometry} (v : g.Valid) {c capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g c capacity p s) (minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1)
    (odd : c % 2 = 1) (large : 1 < c) :
    WP isa code s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c ∧
      word t.mem g.W (g.array 27 + 8 * g.w) = Marker c ∧
      WorkspaceFrame g (preparedRanges g) s.mem t.mem ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps Exponent.clob s t := by
  have words : g.words = 2 * g.w := rfl
  have fit27 := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have nowrap := S.scratch.nowrap
  unfold code marker
  refine WP.seq (WP.seq (WP.mono (scan_ok v S) fun a ⟨V, F, K⟩ => ?_))
  obtain ⟨Sa, Wa⟩ := Ready.keepStack v S K (by decide) (by decide) F
  have selected : (a.gpr .esi ++ a.gpr .ebx).toNat =
      (c - 1) / 2 ^ (64 * ((Spec.Rsa.splitTwos (c - 1)).1 / 64)) % 2 ^ 64 := by
    have pair := congrArg (fun q : BitVec 32 × BitVec 32 => q.2 ++ q.1) V
    dsimp only at pair
    rw [pair]
    exact VG.Proof.RsaKeyGen.X86.LowPair.first_twos (count := g.w) (by rw [← words]; exact minusOne) (by omega_using [large])
  refine WP.mono (markerStore_ok v Sa large selected) fun b ⟨Sb, markerB, _, Ob, Kb⟩ => ?_
  have candidate : val32 b.mem g.W (g.array 0) g.words = c := Sb.modulus.candidate
  refine WP.seq (WP.mono (copyTops_ok v Sb) fun d ⟨Sd, Vd, topD, maskD, markerD, Od, Kd⟩ => ?_)
  refine WP.seq (WP.mono (halfStage_ok v Sd topD maskD) fun e ⟨Se, Ve, topE, markerE, _, Oe, Ke⟩ => ?_)
  have index : (Spec.Rsa.splitTwos (c - 1)).1 % 64 < 64 := Nat.mod_lt _ (by decide)
  have markerE' : word e.mem g.W 136 = Marker c := by rw [markerE, markerD, markerB]
  refine WP.seq (WP.mono (halfIf_ok v Se topE (j := 1) index (by decide) markerE')
    fun f ⟨Sf, Vf, topF, markerF, _, Of, Kf⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_ok v Sf topF (j := 2) index (by decide) markerF)
    fun h ⟨Sh, Vh, topH, markerH, _, Oh, Kh⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_ok v Sh topH (j := 3) index (by decide) markerH)
    fun i ⟨Si, Vi, _, markerI, Pi, Oi, Ki⟩ => ?_)
  refine WP.mono (finish_ok v Si.scratch Pi) fun t ⟨wordT, Ot, Kt⟩ => ?_
  have Ot' : Outs g.W (preparedRanges g) i.mem t.mem := outs27 Ot (by omega_using []) (by omega_using [words])
  have Kall : Keeps Exponent.clob s t :=
    ((((((((K.mono (by decide)).trans Kb).trans Kd).trans Ke).trans Kf).trans Kh).trans Ki).trans
      (Kt.mono (by decide)))
  have Oall : Outs g.W (preparedRanges g) a.mem t.mem :=
    (((((Ob.trans Od).trans Oe).trans Of).trans Oh).trans Oi).trans Ot'
  have chain : val32 i.mem g.W (g.array 27) g.words =
      (let x := c / 2
       let x1 := if 1 < VG.Proof.RsaKeyGen.sigOf ((Spec.Rsa.splitTwos (c - 1)).1 % 64) then x / 2 else x
       let x2 := if 2 < VG.Proof.RsaKeyGen.sigOf ((Spec.Rsa.splitTwos (c - 1)).1 % 64) then x1 / 2 else x1
       if 3 < VG.Proof.RsaKeyGen.sigOf ((Spec.Rsa.splitTwos (c - 1)).1 % 64) then x2 / 2 else x2) := by
    rw [Vi, Vh, Vf, Ve, Vd, candidate]
    rfl
  rw [VG.Proof.RsaKeyGen.sigOf_mod] at chain
  refine ⟨ready_keep v Si Ot' (Kt.mono (by decide)), ?_, ?_, ?_, ?_, Kall⟩
  · rw [Ot.val32 (Or.inl (by omega_using [])) (by omega_using [words, fit27, nowrap])]
    exact chain.trans (VG.Proof.RsaKeyGen.mrE_halves odd)
  · rw [show g.array 27 + 8 * g.w = g.array 27 + 4 * g.words by omega_using [words], wordT, markerI]
  · exact (Wa.mono fun _ mem => nomatch mem).trans (WorkspaceFrame.of_outs nowrap Oall)
  · have first : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
      F.sub fun r mem => by
        obtain rfl := List.mem_singleton.mp mem
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by decide) S.caller.low⟩
    exact first.trans ((workspaceGlobalFrame Oall (prepared_fits v)).mono
      fun r mem => List.mem_append_left _ mem)

end VG.Proof.RsaKeyGen.X86.MrExponentRt
