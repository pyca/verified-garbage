module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundCall
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.RsaKeyGen.X86.OrLoopRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallbackWord
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32
import VerifiedGarbage.Proof.RsaKeyGen.WitnessSample
import VerifiedGarbage.Proof.Mont.LowUpdate32
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside

/-! ### `RsaKeyGen.X86.WitnessRt.Body`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessRt.Load`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessRt.Sample`, which only this module used -/

section

/-! # A witness sampled in array 6 at the run-time width

The witness, marked odd, is compared with the candidate in array 0, restored,
scanned for its words above the lowest, and its fallback bits forced unless
it is uniform: exactly `Spec.RsaKeyGen.witness`. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRt

theorem markAt_ok {s : State} {W : Addr} {L x n : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x)
    (positive : 0 < n) (fit : x + 4 * n ≤ L) :
    WP isa (.block markAt) s fun t =>
      val32 t.mem W x n = val32 s.mem W x n + (1 - val32 s.mem W x n % 2) ∧
      t.gpr .ebx = s.mem.readW (off W x) 32 ∧ Outside W x 4 s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  have nowrap := hw.nowrap
  unfold markAt
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega_using [positive, fit])) fun b B _ => wp_movS rfl fun c Cc _ =>
    wp_orS rfl fun d D => ?_
  obtain Kd : Keeps [.eax, .ebx] s d := ((B.keeps.mono (by decide)).widen Cc.keeps).widen D.keeps
  obtain wd := hw.of_keeps Kd
  obtain Pd : PtrAt d W .ebp x := by rw [PtrAt, Kd.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr wd Pd (d := 0) (by omega_using [positive, fit])) (ws_write wd (y := x + 0) (n := 4) (by omega_using [positive, fit]))
    fun t T => WP.block_nil ?_
  obtain Mt : t.mem = s.mem.writeW (off W x) (d.gpr .eax) := by
    rw [T.mem, D.mem, Cc.mem, B.mem, Nat.add_zero]
  obtain O : Outside W x 4 s.mem t.mem := by
    rw [Mt]; exact writeW32_outside _ _ _ (by omega_using [fit, nowrap])
  obtain low : w32 t.mem W x = w32 s.mem W x ||| 1 := by
    rw [Mt, w32_write_self, D.gpr, Cc.gpr, B.gpr, Nat.add_zero, BitVec.toNat_or]
    rfl
  refine ⟨val32_low_or_one positive (by omega_using [fit, nowrap]) O low, ?_, O, Kd.widen (T.keeps [])⟩
  rw [(T.keeps []).1 .ebx (by decide), D.other .ebx (by decide), Cc.other .ebx (by decide), B.gpr, Nat.add_zero]

theorem mark_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block mark) s fun t =>
      val32 t.mem g.W (g.array 6) g.words =
        val32 s.mem g.W (g.array 6) g.words + (1 - val32 s.mem g.W (g.array 6) g.words % 2) ∧
      t.gpr .ebx = s.mem.readW (off g.W (g.array 6)) 32 ∧ Outside g.W (g.array 6) 4 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ebp, .edx] s t := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold mark
  refine WP.block_append (WP.mono (C.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_)
  refine WP.mono (markAt_ok (C.ws.of_keeps K) P (n := g.words) (by omega_using [many]) fit) fun t ⟨V, E, O, Kt⟩ => ?_
  rw [M] at V E O
  exact ⟨V, E, O, (K.mono (by decide)).widen Kt⟩

theorem lessArgs_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block lessArgs) s fun t =>
      PtrAt t g.W .esi (g.array 6) ∧ PtrAt t g.W .ebp (g.array 0) ∧ (t.gpr .edx).toNat = 4 * g.words ∧
      t.gpr .ecx = cmask false ∧ t.mem = s.mem ∧ Keeps [.ecx, .edx, .ebp, .esi] s t := by
  obtain ⟨fit, below, many, words⟩ := fits v
  have bound := v.maxWidth
  unfold lessArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (C.ptr v 6 (by decide) .esi (by decide) (by decide)) fun a ⟨Pa, Ma, Ka⟩ => ?_)
  obtain Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (Ca.ptr v 0 (by decide) .ebp (by decide) (by decide)) fun b ⟨Pb, Mb, Kb⟩ => ?_)
  obtain Cb := Ca.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (draw_ok v Cb) fun c ⟨D, Mc, Kc⟩ => ?_)
  refine wp_movS rfl fun d Dd _ => WP.block_nil ⟨?_, ?_, ?_, Dd.gpr, by rw [Dd.mem, Mc, Mb, Ma],
    (((Ka.mono (by decide)).widen Kb).widen Kc).widen Dd.keeps⟩
  · rw [PtrAt, Dd.other .esi (by decide), Kc.1 .esi (by decide), Kb.1 .esi (by decide)]; exact Pa
  · rw [PtrAt, Dd.other .ebp (by decide), Kc.1 .ebp (by decide)]; exact Pb
  · rw [Dd.other .edx (by decide), D, BitVec.toNat_ofNat]; omega_using [words, bound]

theorem less_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa less s fun t =>
      t.gpr .ecx = cmask (decide (val32 s.mem g.W (g.array 6) g.words < val32 s.mem g.W (g.array 0) g.words)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  obtain ⟨fit, below, many, words⟩ := fits v
  unfold less
  refine WP.seq (WP.mono (lessArgs_ok v C) fun d ⟨esi, ebp, edx, ecx, Md, K⟩ => ?_)
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.compareLoop_ok (C.ws.of_keeps K) (x := g.array 6) (y := g.array 0)
    (N := g.words) (by omega_using [many]) (by omega_using [fit]) (by omega_using [fit, below]) esi ebp edx ecx) fun t ⟨Mt, E, Kt⟩ => ?_
  rw [Md] at Mt E
  exact ⟨E, Mt, (K.mono (by decide)).trans Kt⟩

theorem restoreAt_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 4 ≤ L) :
    WP isa (.block restoreAt) s fun t =>
      w32 t.mem W x = (s.gpr .ebx).toNat ∧ Outside W x 4 s.mem t.mem ∧ t.gpr .esi = s.gpr .ecx ∧
      Keeps [.esi] s t := by
  have nowrap := hw.nowrap
  unfold restoreAt
  refine wp_storeS (ea_ptr hw P (d := 0) (by omega_using [fit])) (ws_write hw (y := x + 0) (n := 4) (by omega_using [fit]))
    fun b B => wp_movS rfl fun t T _ => WP.block_nil ?_
  obtain Mt : t.mem = s.mem.writeW (off W x) (s.gpr .ebx) := by rw [T.mem, B.mem, Nat.add_zero]
  refine ⟨by rw [Mt, w32_write_self], by rw [Mt]; exact writeW32_outside _ _ _ (by omega_using [fit, nowrap]), ?_,
    ((B.keeps []).mono (by decide)).widen T.keeps⟩
  rw [T.gpr, B.gpr]

theorem restore_ok {g : Geometry} (v : g.Valid) {s original : State} (C : Context g s)
    (O : Outside g.W (g.array 6) 4 original.mem s.mem)
    (saved : s.gpr .ebx = original.mem.readW (off g.W (g.array 6)) 32) :
    WP isa (.block restore) s fun t =>
      val32 t.mem g.W (g.array 6) g.words = val32 original.mem g.W (g.array 6) g.words ∧
      Outside g.W (g.array 6) 4 original.mem t.mem ∧ t.gpr .esi = s.gpr .ecx ∧
      Keeps [.ebp, .edx, .esi] s t := by
  obtain ⟨fit, -, many, -⟩ := fits v
  have nowrap := C.ws.nowrap
  unfold restore
  refine WP.block_append (WP.mono (C.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_)
  refine WP.mono (restoreAt_ok (C.ws.of_keeps K) P (by omega_using [fit, many])) fun t ⟨low, Ot, E, Kt⟩ => ?_
  rw [M] at Ot
  obtain low' : w32 t.mem g.W (g.array 6) = w32 original.mem g.W (g.array 6) := by
    rw [low, K.1 .ebx (by decide), saved]
  refine ⟨val32_restore_low (by omega_using [many]) (by omega_using [fit, nowrap]) (O.trans Ot) low', O.trans Ot, ?_, (K.mono (by decide)).widen Kt⟩
  rw [E, K.1 .ecx (by decide)]

theorem scanArgs_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block scanArgs) s fun t =>
      PtrAt t g.W .ebp (g.array 6 + 4) ∧ (t.gpr .ecx).toNat = g.words - 1 ∧ t.gpr .ebx = 0#32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp, .ecx, .edx] s t := by
  obtain ⟨fit, -, many, words⟩ := fits v
  have bound := v.maxWidth
  have head := v.headerFit
  have nowrap := C.ws.nowrap
  unfold scanArgs
  simp only [List.singleton_append]
  refine wp_movS rfl fun a A _ => ?_
  obtain Ca := C.keepMem A.keeps (by decide) A.mem
  refine WP.block_append (WP.mono (Ca.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun b ⟨P, Mb, Kb⟩ => ?_)
  refine wp_addS rfl fun c Cc _ => ?_
  obtain Kc : Keeps [.ebx, .ebp, .edx] s c := ((A.keeps.mono (by decide)).widen Kb).widen Cc.keeps
  refine wp_movS (readSrc_ptr (C.ws.of_keeps Kc) (r := .edi) (x := 0) (d := 48)
    (by rw [PtrAt, Kc.1 .edi (by decide)]; exact C.base) (by omega_using [head])) fun d Dd _ =>
    wp_addS rfl fun e E _ => wp_subS rfl fun f F _ => WP.block_nil ?_
  obtain width : (d.gpr .ecx).toNat = g.w := by
    rw [Dd.gpr, Cc.mem, Mb, A.mem]; exact C.width
  refine ⟨?_, ?_, ?_, by rw [F.mem, E.mem, Dd.mem, Cc.mem, Mb, A.mem],
    (((Kc.mono (by decide)).widen Dd.keeps).widen E.keeps).widen F.keeps⟩
  · rw [PtrAt, F.other .ebp (by decide), E.other .ebp (by decide), Dd.other .ebp (by decide), Cc.gpr]
    exact ptr_add P 4
  · rw [F.gpr, E.gpr, BitVec.toNat_sub_of_le, BitVec.toNat_add, width]
    · change (g.w + g.w) % 2 ^ 32 - 1 = g.words - 1
      omega_using [words, bound]
    · rw [BitVec.le_def, BitVec.toNat_add, width]
      change 1 ≤ (g.w + g.w) % 2 ^ 32
      omega
  · rw [F.other .ebx (by decide), E.other .ebx (by decide), Dd.other .ebx (by decide), Cc.other .ebx (by decide),
      Kb.1 .ebx (by decide), A.gpr]
    rfl

theorem scan_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa scan s fun t =>
      (t.gpr .ebx = 0#32 ↔ val32 s.mem g.W (g.array 6 + 4) (g.words - 1) = 0) ∧ t.mem = s.mem ∧
      Keeps [.ebx, .ebp, .ecx, .edx] s t := by
  obtain ⟨fit, -, many, words⟩ := fits v
  unfold scan
  refine WP.seq (WP.mono (scanArgs_ok v C) fun f ⟨Pf, count, zero, Mf, Kf⟩ => ?_)
  refine WP.mono (FrontRt.orLoop_ok (C.ws.of_keeps Kf) (by omega_using [many]) (by omega_using [fit, many]) Pf count zero) fun t ⟨Z, Mt, _, Kt⟩ => ?_
  rw [Mf] at Z Mt
  exact ⟨Z, Mt, Kf.trans (Kt.mono (by decide))⟩

theorem cmask_and (x y : Bool) : cmask x &&& cmask y = cmask (x && y) := by
  cases x <;> cases y <;> rfl

theorem lowerAt_ok {s : State} {W : Addr} {L x n : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x)
    (positive : 0 < n) (fit : x + 4 * n ≤ L) {b : Bool}
    (zero : s.gpr .ebx = 0#32 ↔ val32 s.mem W (x + 4) (n - 1) = 0) (mask : s.gpr .esi = cmask b) :
    WP isa (.block lowerAt) s fun t =>
      t.gpr .eax = cmask (decide (2 ≤ val32 s.mem W x n) && b) ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold lowerAt
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega_using [positive, fit])) fun b0 B _ => wp_orS rfl fun c Cc =>
    wp_logicS (.inr rfl) rfl fun d D => wp_orS rfl fun e E => ?_
  obtain low : d.gpr .eax = (s.mem.readW (off W x) 32 ||| 1#32) ^^^ 1#32 := by
    rw [D.gpr, Cc.gpr, B.gpr, Nat.add_zero]
    rfl
  obtain combined : e.gpr .ebx = s.gpr .ebx ||| ((s.mem.readW (off W x) 32 ||| 1#32) ^^^ 1#32) := by
    rw [E.gpr, low, D.other .ebx (by decide), Cc.other .ebx (by decide), B.other .ebx (by decide)]
  obtain combinedZero : (e.gpr .ebx).toNat = 0 ↔ ¬ 2 ≤ val32 s.mem W x n := by
    rw [show (e.gpr .ebx).toNat = 0 ↔ e.gpr .ebx = 0#32 from @BitVec.toNat_inj 32 (e.gpr .ebx) (0#32),
      combined, BitVec.or_eq_zero_iff, zero, WitnessLower.clear_low_zero, Nat.not_le,
      WitnessLower.below_two _ _ _ _ positive]
  refine wp_cmpi fun f F cf _ => wp_sbb_self cf fun h H => wp_logicS (.inr rfl) rfl fun i I =>
    wp_movS rfl fun j J _ => wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  obtain Ki : Keeps [.eax, .ebx] s i :=
    ((((((B.keeps.mono (by decide)).widen Cc.keeps).widen D.keeps).widen E.keeps).trans
      (F.keeps _)).widen H.keeps).widen I.keeps
  obtain ebx : i.gpr .ebx = cmask (decide (2 ≤ val32 s.mem W x n)) := by
    rw [I.gpr, H.gpr]
    change cmask (decide ((e.gpr .ebx).toNat < 1)) ^^^ BitVec.allOnes 32 = _
    rw [SigMask.flip_mask]
    exact congrArg cmask (decide_eq_decide.mpr
      ⟨fun h' => Decidable.byContradiction fun h'' => h' (combinedZero.mpr h''), fun h' h'' => combinedZero.mp h'' h'⟩)
  refine ⟨?_, by rw [T.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, Cc.mem, B.mem],
    (Ki.widen J.keeps).widen T.keeps⟩
  have Tv : t.gpr .eax = j.gpr .eax &&& j.gpr .ebx := T.gpr
  rw [Tv, J.gpr, J.other .ebx (by decide), ebx, Ki.1 .esi (by decide), mask, cmask_and, Bool.and_comm]

theorem lower_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) {b : Bool}
    (zero : s.gpr .ebx = 0#32 ↔ val32 s.mem g.W (g.array 6 + 4) (g.words - 1) = 0)
    (mask : s.gpr .esi = cmask b) :
    WP isa (.block lower) s fun t =>
      t.gpr .eax = cmask (decide (2 ≤ val32 s.mem g.W (g.array 6) g.words) && b) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ebp, .edx] s t := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold lower
  refine WP.block_append (WP.mono (C.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_)
  refine WP.mono (lowerAt_ok (b := b) (C.ws.of_keeps K) P (n := g.words) (by omega_using [many]) fit
    (by rw [K.1 .ebx (by decide), M]; exact zero) (by rw [K.1 .esi (by decide)]; exact mask))
    fun t ⟨E, Mt, Kt⟩ => ?_
  rw [M] at E
  exact ⟨E, Mt.trans M, (K.mono (by decide)).widen Kt⟩

theorem fallbackLow_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x)
    (fit : x + 4 ≤ L) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block fallbackLow) s fun t =>
      w32 t.mem W x = (if uniform then w32 s.mem W x else w32 s.mem W x ||| 2) ∧
      Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackLow
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  obtain Kc : Keeps [.ecx] s c := (A.keeps.widen B.keeps).widen C.keeps
  obtain Pc : PtrAt c W .ebp x := by rw [PtrAt, Kc.1 .ebp (by decide)]; exact P
  obtain load := readSrc_ptr (hw.of_keeps Kc) Pc (d := 0) (by omega_using [fit])
  rw [C.mem, B.mem, A.mem, Nat.add_zero] at load
  refine wp_orS load fun d D => ?_
  obtain Kd : Keeps [.ecx] s d := Kc.widen D.keeps
  obtain wd := hw.of_keeps Kd
  obtain Pd : PtrAt d W .ebp x := by rw [PtrAt, Kd.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr wd Pd (d := 0) (by omega_using [fit])) (ws_write wd (y := x + 0) (n := 4) (by omega_using [fit]))
    fun t T => WP.block_nil ?_
  obtain V : d.gpr .ecx = (((cmask uniform ^^^ BitVec.allOnes 32) &&& 2#32) ||| s.mem.readW (off W x) 32) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Kd.widen (T.keeps [])⟩
  · rw [T.mem, Nat.add_zero, w32_write_self, V]
    exact WitnessFallback.low_value _ _
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega_using [fit, this])

theorem fallbackHigh_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebx x)
    (fit : x + 4 ≤ L) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block fallbackHigh) s fun t =>
      w32 t.mem W x = (if uniform then w32 s.mem W x else w32 s.mem W x % 2 ^ 31) ∧
      Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackHigh
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B =>
    wp_logicS (.inl rfl) rfl fun c C => wp_logicS (.inr rfl) rfl fun d D => ?_
  obtain Kd : Keeps [.ecx] s d := ((A.keeps.widen B.keeps).widen C.keeps).widen D.keeps
  obtain Pd : PtrAt d W .ebx x := by rw [PtrAt, Kd.1 .ebx (by decide)]; exact P
  obtain load := readSrc_ptr (hw.of_keeps Kd) Pd (d := 0) (by omega_using [fit])
  rw [D.mem, C.mem, B.mem, A.mem, Nat.add_zero] at load
  refine wp_logicS (.inl rfl) load fun e E => ?_
  obtain Ke : Keeps [.ecx] s e := Kd.widen E.keeps
  obtain we := hw.of_keeps Ke
  obtain Pe : PtrAt e W .ebx x := by rw [PtrAt, Ke.1 .ebx (by decide)]; exact P
  refine wp_storeS (ea_ptr we Pe (d := 0) (by omega_using [fit])) (ws_write we (y := x + 0) (n := 4) (by omega_using [fit]))
    fun t T => WP.block_nil ?_
  obtain V : e.gpr .ecx = ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 0x80000000#32) ^^^
      BitVec.allOnes 32) &&& s.mem.readW (off W x) 32) := by
    rw [E.gpr, D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Ke.widen (T.keeps [])⟩
  · rw [T.mem, Nat.add_zero, w32_write_self, V]
    exact WitnessFallback.high_value _ _
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega_using [fit, this])

theorem fallbackTop_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (P : PtrAt s g.W .ebp (g.array 6)) :
    WP isa (.block fallbackTop) s fun t =>
      PtrAt t g.W .ebx (g.array 6 + 4 * g.words - 4) ∧ t.mem = s.mem ∧ Keeps [.ebx, .edx] s t := by
  obtain ⟨fit, -, many, words⟩ := fits v
  have bound := v.maxWidth
  have nowrap := C.ws.nowrap
  unfold fallbackTop
  refine WP.block_append (WP.mono (draw_ok v C) fun c ⟨D, Mc, Kc⟩ => ?_)
  refine wp_movS rfl fun d Dd _ => wp_addS rfl fun e E _ => wp_subS rfl fun f F _ => WP.block_nil ?_
  obtain ebp : (c.gpr .ebp).toNat = (g.W.toNat + g.array 6) % 2 ^ 32 := by
    rw [Kc.1 .ebp (by decide)]; exact P
  obtain sum : PtrAt e g.W .ebx (g.array 6 + 4 * g.words) := by
    rw [PtrAt, E.gpr, Dd.gpr, Dd.other .edx (by decide), ptr_add ebp, D, BitVec.toNat_ofNat]
    congr 2
    omega_using [words, bound]
  refine ⟨?_, by rw [F.mem, E.mem, Dd.mem, Mc], (((Kc.mono (by decide)).widen Dd.keeps).widen E.keeps).widen F.keeps⟩
  rw [PtrAt, F.gpr, ptr_sub sum 4 (by change 4 ≤ _; omega_using [many])]
  rfl

theorem fallback_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) {uniform : Bool}
    (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block fallback) s fun t =>
      val32 t.mem g.W (g.array 6) g.words =
        (if uniform then val32 s.mem g.W (g.array 6) g.words
          else (val32 s.mem g.W (g.array 6) g.words ||| 2) % 2 ^ (32 * g.words - 1)) ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.ebx, .ecx, .ebp, .edx] s t := by
  obtain ⟨fit, -, many, words⟩ := fits v
  have bound := v.maxWidth
  have nowrap := C.ws.nowrap
  obtain header := v.arrayHeader 6
  unfold fallback
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (C.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_)
  obtain Ca := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (fallbackLow_ok (uniform := uniform) Ca.ws P (by omega_using [fit, many]) (by rw [K.1 .eax (by decide)]; exact mask))
    fun b ⟨low, Ob, Kb⟩ => ?_)
  obtain Cb := Ca.keepOutside Kb (by decide) Ob header
  refine WP.block_append (WP.mono (fallbackTop_ok v Cb (by rw [PtrAt, Kb.1 .ebp (by decide)]; exact P))
    fun f ⟨Pf, Mf, Kcf⟩ => ?_)
  obtain Kf : Keeps [.ebx, .ecx, .ebp, .edx] s f := (((K.mono (by decide)).widen Kb).widen Kcf)
  refine WP.mono (fallbackHigh_ok (uniform := uniform) (Cb.ws.of_keeps Kcf)
    Pf (by omega_using [fit, many]) (by
      rw [Kcf.1 .eax (by decide), Kb.1 .eax (by decide), K.1 .eax (by decide)]
      exact mask)) fun t ⟨top, Ot, Kt⟩ => ?_
  rw [Mf] at top Ot
  rw [M] at low Ob
  obtain lowSame : w32 t.mem g.W (g.array 6) = w32 b.mem g.W (g.array 6) := Ot.w32 (by omega_using [many]) (by omega_using [fit, nowrap])
  obtain topSame : w32 b.mem g.W (g.array 6 + 4 * g.words - 4) = w32 s.mem g.W (g.array 6 + 4 * g.words - 4) :=
    Ob.w32 (by omega_using [many]) (by omega_using [fit, nowrap])
  refine ⟨?_, (Ob.mono (by omega_using []) (by omega_using [many])).trans (Ot.mono (by omega_using [many]) (by omega_using [many])), Kf.widen Kt⟩
  cases uniform
  · simp only [Bool.false_eq_true, ↓reduceIte] at low top ⊢
    apply VG.Proof.RsaKeyGen.val32_witness_fallback (by omega_using [many])
    · rw [lowSame, low]
    · rw [show g.array 6 + 4 * (g.words - 1) = g.array 6 + 4 * g.words - 4 by omega_using [many], top, topSame]
    · intro j first last
      exact (Ot.w32 (by omega_using [last]) (by omega_using [fit, nowrap, last])).trans (Ob.w32 (by omega_using [first]) (by omega_using [fit, nowrap, last]))
  · simp only [↓reduceIte] at low top ⊢
    apply val32_congr
    intro j hj
    by_cases first : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using lowSame.trans low
    · by_cases last : j = g.words - 1
      · subst j
        rw [show g.array 6 + 4 * (g.words - 1) = g.array 6 + 4 * g.words - 4 by omega_using [many]]
        exact top.trans topSame
      · exact (Ot.w32 (by omega_using [last]) (by omega_using [fit, nowrap, hj])).trans (Ob.w32 (by omega_using [first]) (by omega_using [fit, nowrap, hj]))

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem sample_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) {c x : Nat}
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (witness : val32 s.mem g.W (g.array 6) g.words = x)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * g.words) :
    WP isa sample s fun t =>
      val32 t.mem g.W (g.array 6) g.words = (Spec.RsaKeyGen.witness (c - 1) x).1 ∧
      t.gpr .eax = cmask (Spec.RsaKeyGen.witness (c - 1) x).2 ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t ∧ Context g t := by
  obtain ⟨fit, below, many, -⟩ := fits v
  have nowrap := C.ws.nowrap
  obtain header := v.arrayHeader 6
  obtain bound : x < 2 ^ (32 * g.words) := witness ▸ val32_lt s.mem g.W (g.array 6) g.words
  obtain sampled := VG.Proof.RsaKeyGen.witness_sampleAt shape bound
  unfold sample
  refine WP.seq (WP.mono (mark_ok v C) fun a ⟨Va, saved, Oa, Ka⟩ => ?_)
  rw [witness] at Va
  obtain Ca := C.keepOutside Ka (by decide) Oa header
  refine WP.seq (WP.mono (less_ok v Ca) fun b ⟨lt, Mb, Kb⟩ => ?_)
  obtain Cb := Ca.keepMem Kb (by decide) Mb
  obtain modA : val32 a.mem g.W (g.array 0) g.words = c := by
    rw [Oa.val32 (by omega_using [below]) (by omega_using [fit, below, nowrap])]; exact candidate
  rw [Va, modA] at lt
  refine WP.seq (WP.mono (restore_ok (original := s) v Cb (by rw [Mb]; exact Oa)
    (by rw [Kb.1 .ebx (by decide)]; exact saved)) fun d ⟨Vd, Od, esi, Kd⟩ => ?_)
  rw [witness] at Vd
  obtain Kad : Keeps clob s d := (((Ka.mono (by unfold clob; decide)).widen Kb (by unfold clob; decide)).widen Kd
    (by unfold clob; decide))
  obtain Cd := C.keepOutside Kad (by unfold clob; decide) Od header
  refine WP.seq (WP.mono (scan_ok v Cd) fun e ⟨Z, Me, Ke⟩ => ?_)
  rw [← Me] at Z
  obtain Ce := Cd.keepMem Ke (by decide) Me
  refine WP.block_append (WP.mono (lower_ok v Ce Z (b := decide (x + (1 - x % 2) < c))
    (by rw [Ke.1 .esi (by decide), esi, lt])) fun f ⟨eax, Mf, Kf⟩ => ?_)
  obtain Cf := Ce.keepMem Kf (by decide) Mf
  obtain Ve : val32 e.mem g.W (g.array 6) g.words = x := by rw [Me]; exact Vd
  obtain uniform : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = decide (2 ≤ x ∧ x < c - 1) := by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr (by omega_using [odd])
  rw [Ve, uniform] at eax
  refine WP.mono (fallback_ok v Cf eax) fun t ⟨V, Ot, Kt⟩ => ?_
  rw [Mf, Ve] at V
  rw [Mf, Me] at Ot
  obtain O : Outside g.W (g.array 6) (4 * g.words) s.mem t.mem := (Od.mono (by omega_using []) (by omega_using [many])).trans Ot
  obtain K : Keeps clob s t := ((Kad.widen Ke (by unfold clob; decide)).widen Kf (by unfold clob; decide)).widen Kt
    (by unfold clob; decide)
  refine ⟨?_, ?_, O, K, C.keepOutside K (by unfold clob; decide) O header⟩
  · rw [sampled]; exact V
  · rw [Kt.1 .eax (by decide), eax, sampled]

end VG.Proof.RsaKeyGen.X86.WitnessRt

end

end


/-! # A witness drawn from the entropy into array 6 and sampled, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRt

theorem importArgs_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) {input : Import.Geometry}
    (count : input.count = g.words) (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst) :
    WP isa (.block importArgs) s fun t =>
      t.mem = s.mem ∧ Keeps [.ebx, .ecx, .edx] s t ∧ t.gpr .esi = input.sourcePtr 0 ∧
      t.gpr .ebx = input.destPtr 0 ∧ t.gpr .ecx = BitVec.ofNat 32 input.count := by
  obtain ⟨fit, -, many, words⟩ := fits v
  have bound := v.maxWidth
  have head := v.headerFit
  have nowrap := C.ws.nowrap
  unfold importArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (draw_ok v C) fun a ⟨D, Ma, Ka⟩ => ?_)
  obtain Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (ptr_short v Ca 6 (by decide) .ebx) fun b ⟨P, Mb, Kb⟩ => ?_)
  refine wp_addS rfl fun c Cc _ => wp_subS rfl fun d Dd _ => ?_
  obtain Kd : Keeps [.ebx, .edx] s d := (((Ka.mono (by decide)).widen Kb).widen Cc.keeps).widen Dd.keeps
  refine wp_movS (readSrc_ptr (C.ws.of_keeps Kd) (r := .edi) (x := 0) (d := 48)
    (by rw [PtrAt, Kd.1 .edi (by decide)]; exact C.base) (by omega_using [head])) fun e E _ =>
    wp_addS rfl fun t T _ => WP.block_nil ?_
  obtain K : Keeps [.ebx, .ecx, .edx] s t := ((Kd.mono (by decide)).widen E.keeps).widen T.keeps
  obtain edx : (b.gpr .edx).toNat = 8 * g.w := by
    rw [Kb.1 .edx (by decide), D, BitVec.toNat_ofNat]; omega_using [bound]
  obtain sum : PtrAt c g.W .ebx (g.array 6 + 8 * g.w) := by
    rw [PtrAt, Cc.gpr, ptr_add P, edx]
  obtain ebx : PtrAt d g.W .ebx (g.array 6 + 8 * g.w - 4) := by
    rw [PtrAt, Dd.gpr, ptr_sub sum 4 (by change 4 ≤ _; omega_using [many, words])]
    rfl
  have base := C.base
  refine ⟨by rw [T.mem, E.mem, Dd.mem, Cc.mem, Mb, Ma], K, ?_, ?_, ?_⟩
  · rw [K.1 .esi (by decide), source]
    simp only [Import.Geometry.sourcePtr, Nat.mul_zero, BitVec.add_zero]
  · rw [T.other .ebx (by decide), E.other .ebx (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [ebx]
    unfold Import.Geometry.destPtr
    rw [← destination, count, Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.sub_zero,
      BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, base]
    omega_using [many, words]
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr, BitVec.toNat_add, E.gpr, BitVec.toNat_ofNat, count]
    change (w32 d.mem g.W 48 + w32 d.mem g.W 48) % 2 ^ 32 = _
    rw [Dd.mem, Cc.mem, Mb, Ma, C.width]
    omega_using [words]

theorem load_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry} (I : Import.Context input s)
    (count : input.count = g.words) (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst) :
    WP isa load s fun t =>
      Prepare.Data g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * g.words)) ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  obtain ⟨fit, -, many, -⟩ := fits v
  have nowrap := S.ready.scratch.nowrap
  refine WP.seq (WP.mono (importArgs_ok v S.ready.context count source destination)
    fun a ⟨M, K, Ps, Pd, Pc⟩ => ?_)
  obtain Ia : Import.Context input a := ⟨I.positive, I.sourceFit, I.destFit,
    fun i index => by rw [K.2.1, K.2.2]; exact I.readable i index,
    fun i index => by rw [K.2.2]; exact I.writable i index, I.separate⟩
  refine WP.mono (Import.code_ok Ia Ps Pd Pc) fun t T => ?_
  have value := T.os2ip
  have F := T.frame
  rw [M] at value F
  obtain dstAddr : input.dst.setWidth 64 = off g.W (g.array 6) := by
    rw [← destination]
    exact S.ready.scratch.ea (d := g.array 6) (by omega_using [fit, many])
  obtain region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr]
  rw [region, count] at F
  rw [dstAddr, count, VG.Proof.Bignum.read_eq_val32] at value
  obtain O := frame_outside F (by omega_using [fit, nowrap])
  obtain Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := (K.mono (by decide)).trans (T.keeps.mono (by decide))
  exact ⟨WitnessMont.data_outside v S O Kt (by decide) (by decide), value, O, Kt⟩

theorem drawn_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry} (I : Import.Context input s)
    (count : input.count = g.words) (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w) :
    WP isa drawn s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t := by
  obtain ⟨-, -, -, words⟩ := fits v
  refine WP.seq (WP.mono (load_ok v S I count source destination) fun a ⟨A, Va, Oa, Ka⟩ => ?_)
  rw [show 4 * g.words = 8 * g.w by omega_using [words]] at Va
  refine WP.mono (sample_ok v A.ready.context A.ready.modulus.candidate Va odd (by rw [shape]; omega_using [words]))
    fun t ⟨Vt, mask, Ot, Kt, _⟩ => ?_
  exact ⟨WitnessMont.data_outside v A Ot Kt (by unfold clob; decide) (by unfold clob; decide), Vt, mask,
    Oa.trans Ot, (Ka.mono (by unfold clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt

end

end

/-! ### `RsaKeyGen.X86.WitnessRt.Round`, which only this module used -/

section

/-! # Each witness iteration at the run-time width computes the exact sampled Miller–Rabin test -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRound (uniformOffset)

theorem round_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) (count : input.count = g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.round montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c sampled.1 then 1 else 0) ∧
      t.mem.readW (off g.W uniformOffset) 32 = cmask sampled.2 ∧
      WorkspaceFrame g (WitnessRound.ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps WitnessRound.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.round
  refine WP.seq (WP.mono (drawn_ok v S C count source destination odd shape)
    fun a ⟨A, Va, uniform, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Prepare.storeGap_ok v A (d := uniformOffset) (by decide) (by decide))
    fun b ⟨B, uniformB, Ob, Kb⟩ => ?_)
  rw [uniform] at uniformB
  have Vb := (Ob.val32 (Or.inr (by have := v.arrayHeader 6; unfold uniformOffset; omega_using [this]))
    (by have := A.ready.scratch.nowrap; have := v.arrayFit (j := 6) (by decide); omega_arith)).trans Va
  refine WP.seq (WP.mono (WitnessMont.code_ok montVerified montNoSp montStack v length B odd (by omega_using [odd]))
    fun d ⟨D, Vd, Wd, Fd, Kd⟩ => ?_)
  rw [Vb] at Vd
  have uniformD : d.mem.readW (off g.W uniformOffset) 32 = b.mem.readW (off g.W uniformOffset) 32 :=
    Wd.read32 (by have := v.headerFit; unfold uniformOffset; omega_using [this]) (fun r mem => by
      simp only [WitnessMont.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | rfl <;>
        exact Or.inl (by simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))
  refine WP.mono (RoundCall.code_ok (b := (Spec.RsaKeyGen.witness (c - 1)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))).1)
    roundVerified roundNoSp roundStack v length D odd large
    (by rw [Nat.mod_mul_mod]; exact Vd) fit far lengthFar) fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have uniformT : t.mem.readW (off g.W uniformOffset) 32 = d.mem.readW (off g.W uniformOffset) 32 :=
    Wt.read32 (by have := v.headerFit; unfold uniformOffset; omega_using [this]) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [])
  have Wa : WorkspaceFrame g (WitnessRound.ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.ready.scratch.nowrap (Outs.of_outside
      (Oa.mono (o' := g.array 6) (n' := 8 * (g.w + 2)) (Nat.le_refl _) (by unfold Geometry.words; omega_using []))
      (by simp [WitnessRound.ranges, WitnessMont.ranges, montWrites]))
  have Wb : WorkspaceFrame g (WitnessRound.ranges g) a.mem b.mem :=
    WorkspaceFrame.of_outs A.ready.scratch.nowrap (Outs.of_outside Ob (by simp [WitnessRound.ranges]))
  have Wd' := Wd.mono (fun r mem => List.mem_append_left _ (List.mem_append_left _ mem) : ∀ r ∈ WitnessMont.ranges g, r ∈ WitnessRound.ranges g)
  have Wt' := Wt.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ roundWrites g, r ∈ WitnessRound.ranges g)
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fb : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) a.mem b.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ob (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold uniformOffset; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fd' := VG.X86.Frame.below_mono Fd (by decide : 80 ≤ 108) fit
  exact ⟨T, result, (uniformT.trans uniformD).trans uniformB,
    ((Wa.trans Wb).trans Wd').trans Wt', ((Fa.trans Fb).trans Fd').trans Ft,
    (((Ka.mono (by unfold WitnessRound.clob WitnessRt.clob; decide)).widen Kb).widen Kd).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt

end

end


/-! # A witness step at the run-time width accounts for entropy and both witness counters exactly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity used randLen : Nat} {p rand : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand) (consumed : w32 s.mem g.W 152 = used)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w)
    (roundsFit : w32 s.mem g.W 176 + 1 < 2 ^ 32) (uniformFit : w32 s.mem g.W 192 + 1 < 2 ^ 32)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 152 = used + 8 * g.w ∧
      w32 t.mem g.W 176 = w32 s.mem g.W 176 + 1 ∧
      w32 t.mem g.W 192 = w32 s.mem g.W 192 + sampled.2.toNat ∧
      w32 t.mem g.W 168 = WitnessStatus.status (Proof.MillerRabin.Round.round c sampled.1)
        (w32 s.mem g.W 176 + 1) (w32 s.mem g.W 192 + sampled.2.toNat) (w32 s.mem g.W 200) ∧
      WorkspaceFrame g (WitnessStep.ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have bound := v.maxWidth
  have words : g.words = 2 * g.w := rfl
  have positive := v.minWidth
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.body
  refine WP.seq (WP.mono (advance_ok v S source consumed (by omega_using [randLenFit, enough]))
    fun a ⟨A, sourceA, usedA, Oa, Ka⟩ => ?_)
  let input := WitnessInput.geometryAt g rand used g.words
  have readA : InRegions (a.rd ++ a.wr) (rand.setWidth 64) randLen := by
    rw [Ka.2.1, Ka.2.2]; exact readable
  have C := WitnessInput.context_okAt (used := used) (count := g.words) v A.ready.scratch randFit (by omega_using [words, positive])
    (by unfold Geometry.words; omega_using []) (by omega_using [enough, words]) readA separate
  have inputSource : input.src.setWidth 64 = off (rand.setWidth 64) used :=
    WitnessInput.source_address (by omega_using [randFit, enough, positive])
  have bytesA : Spec.Rsa.bytesAt a.mem (input.src.setWidth 64) (8 * g.w) =
      Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) (8 * g.w) := by
    rw [inputSource]
    apply VG.Proof.Bignum.scratch_bytes
      (Oa.mono (o' := 0) (n' := g.L) (by decide) (by have := v.headerFit; omega_using [this]))
      (by have := randLenFit; omega_using [bound])
    exact separate.sub_left (Offset.sub_base _ enough)
  refine WP.seq (WP.mono (round_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v length A
    C rfl sourceA
    (WitnessInput.destination_pointer v A.ready.scratch).symm odd large shape fit far lengthFar)
    fun b ⟨B, resultB, uniformB, Wb, Fb, Kb⟩ => ?_)
  rw [bytesA] at resultB uniformB
  have roundB : w32 b.mem g.W 176 = w32 s.mem g.W 176 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by decide) (by decide))
  have uniB : w32 b.mem g.W 192 = w32 s.mem g.W 192 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by decide) (by decide))
  have checksB : w32 b.mem g.W 200 = w32 s.mem g.W 200 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by decide) (by decide))
  have flagB : b.gpr .eax = BitVec.ofNat 32 (Proof.MillerRabin.Round.round c
      (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) (8 * g.w)))).1).toNat := by
    exact WitnessStep.flag_value resultB
  refine WP.mono (WitnessCount.code_ok v B flagB uniformB (by change w32 b.mem g.W 176 + 1 < 2 ^ 32; rw [roundB]; exact roundsFit)
    (by change w32 b.mem g.W 192 + _ < 2 ^ 32; rw [uniB]; have := Bool.toNat_le (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) (8 * g.w)))).2; omega_using [uniformFit, this]))
    fun t ⟨T, countT, uniT, statusT, Ot, Kt⟩ => ?_
  dsimp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
    VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.checksOffset] at countT uniT statusT
  rw [roundB] at countT
  rw [uniB] at uniT
  rw [roundB, uniB, checksB] at statusT
  have usedB := (WitnessRound.header32 v Wb (d := 152) (by unfold WitnessRound.safeHeader; decide)).trans usedA
  have usedT : w32 t.mem g.W 152 = used + 8 * g.w := by
    have same := (WorkspaceFrame.of_outs B.ready.scratch.nowrap Ot).read32
      (d := 152) (by have := v.headerFit; omega_using [this]) (by
        intro r mem
        simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with (rfl | rfl) | rfl <;> left <;> decide)
    rw [show w32 t.mem g.W 152 = w32 b.mem g.W 152 from congrArg BitVec.toNat same]
    exact usedB
  have Wa : WorkspaceFrame g (WitnessStep.ranges g) s.mem a.mem := WorkspaceFrame.of_outs S.ready.scratch.nowrap
    (Outs.of_outside Oa (by simp [WitnessStep.ranges]))
  have Wb' := Wb.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ WitnessRound.ranges g, r ∈ WitnessStep.ranges g)
  have Wt : WorkspaceFrame g (WitnessStep.ranges g) b.mem t.mem := WorkspaceFrame.of_outs B.ready.scratch.nowrap
    (Ot.mono (fun r mem => List.mem_append_right _ mem))
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) b.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl) | rfl <;> have := v.headerFit <;>
        simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
          VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨T, usedT, countT, uniT, statusT, (Wa.trans Wb').trans Wt, (Fa.trans Fb).trans Ft,
    ((Ka.mono (by unfold WitnessStep.clob; decide)).widen Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt

end

end

/-! # The blinded witness loop at the run-time width

`MillerRabinLoop.code_ok` for the loop whose width, witness octets and
required tests come from the prepared header: RSA's parameters (`Fixed`). -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop (exhausted again)

/-- The parameters the run-time loop computes from the width: RSA's. -/
structure Fixed (P : Parameters) : Prop where
  bytes : P.bytes = 8 * P.g.w
  words : P.words = 2 * P.g.w
  checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w

theorem drawRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧
      w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes ∧ w32 t.mem P.g.W 176 = k + 1 ∧
      w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2 ∧
      w32 t.mem P.g.W 168 =
        (if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
            (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
          if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
        else 3) ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have counts := S.countFit v
  refine WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v.geometry
    v.length S.prepared S.randPtr S.used v.randFit v.randLenFit (by rw [← Fx.bytes]; exact enough) S.readable
    v.randSeparate v.odd (by have := v.large; omega_using [this]) (by rw [v.shape, Fx.words]; omega_using []) counts.1 counts.2 v.low
    v.stackFar v.lengthFar) fun t ⟨T, used, rounds, uniform, status, W, F, K⟩ => ?_
  rw [← Fx.bytes] at used uniform status
  rw [S.rounds] at rounds
  rw [S.sample enough, S.uniform, ← mrSB_uniform_next] at uniform
  rw [S.sample enough, S.rounds, S.uniform, S.checks, count_policy] at status
  exact ⟨T, used, rounds, uniform, status, W, F, K⟩

theorem drawRt_again_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (drawRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx S enough)
    fun a ⟨A, usedA, roundsA, uniformA, statusA, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem := by rw [mem]; exact Wa
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem := by rw [mem]; exact Fa
  refine ⟨T, ?_, W, F, Ka.widen Kt⟩
  have ev : isa.eval .e t = some (decide (w32 a.mem P.g.W 168 = 4)) := Z
  cases passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 with
  | false =>
    have failed := S.failed v enough passed
    simp only [passed] at statusA
    refine Or.inl ⟨?_, failed.1, ?_⟩
    · rw [ev, statusA]; rfl
    · unfold Result
      rw [failed.2, mem]
      refine ⟨statusA, ?_⟩
      rw [usedA, List.length_drop]
      have bound := enough
      rw [← v.entropyLength] at bound
      omega_using [bound]
  | true =>
    by_cases more : goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))
    · have next := mrLoopAt_next S.atLoop v.witnessBytes
        (by have := v.narrow; have := v.two; omega_arith)
        (by rw [v.entropyLength]; exact enough) passed more
      simp only [passed, ↓reduceIte, more] at statusA
      have nextState := StateAt.next v S A usedA roundsA uniformA next.2 Wa Fa Ka
      refine Or.inr ⟨?_, next.1, nextState.keepMem v mem Kt (by decide) (by decide)⟩
      rw [ev, statusA]; rfl
    · have done := S.accepted v enough passed more
      simp only [passed, ↓reduceIte, more] at statusA
      refine Or.inl ⟨?_, done.1, ?_⟩
      · rw [ev, statusA]; rfl
      · unfold Result
        rw [done.2, mem]
        refine ⟨statusA, ?_⟩
        rw [usedA, List.length_drop]
        have bound := enough
        rw [← v.entropyLength] at bound
        omega_using [bound]

theorem stepRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used
    rw [v.entropyLength] at this
    exact this
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.step
  refine WP.seq (WP.mono (available_ok v.geometry S.prepared.ready.scratch S.prepared.ready.context S.randLength
    S.used usedBound) fun a ⟨CF, mem, Ka⟩ => ?_)
  have A := S.keepMem v mem Ka (by decide) (by decide)
  have condition : isa.eval .b a = some (decide (¬ P.start + P.bytes * k + P.bytes ≤ P.randLen)) := by
    change a.cf = _
    rw [CF]
    congr 1
    apply decide_eq_decide.mpr
    rw [← Fx.bytes]
    omega_using [usedBound]
  refine WP.seq ?_
  by_cases enough : P.start + P.bytes * k + P.bytes ≤ P.randLen
  · refine WP.ite false (by rw [condition]; simp only [enough, not_true_eq_false, decide_false])
      (fun impossible => nomatch impossible) (fun _ => ?_)
    apply WP.seq_iff.mp
    refine WP.mono (drawRt_again_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx A enough)
      fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite true (by rw [condition]; simp only [enough, not_false_eq_true, decide_true])
      (fun _ => ?_) (fun impossible => nomatch impossible)
    apply WP.seq_iff.mp
    refine WP.mono (exhausted_again_ok v A enough) fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

theorem initRt_ok {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State}
    (S : Prepare.Data P.g P.candidate P.capacity P.p s)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.WitnessRt.checks) s fun t =>
      StateAt P 0 (itersOf P.bytes P.entropy.length
        (shapeOf P.test) P.start - 1) t ∧
      WorkspaceFrame P.g WitnessChecks.ranges s.mem t.mem ∧ Frame [⟨P.g.W, P.g.L⟩] s.mem t.mem ∧
      Keeps [.eax, .ecx] s t := by
  refine WP.mono (checks_ok v.geometry S) fun t ⟨T, roundsT, uniformT, checksT, O, K⟩ => ?_
  rw [← Fx.checks] at checksT
  have rangesFit : ∀ r ∈ WitnessChecks.ranges, r.1 + r.2 ≤ P.g.L := by
    intro r mem
    simp only [WitnessChecks.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> have := v.geometry.headerFit <;> omega_using [this]
  have W := WorkspaceFrame.of_outs S.ready.scratch.nowrap O
  have F := workspaceGlobalFrame O rangesFit
  have hdr {d : Nat} (bound : d + 4 ≤ 176) : w32 t.mem P.g.W d = w32 s.mem P.g.W d := by
    apply congrArg BitVec.toNat
    apply W.read32 (by have := v.geometry.headerFit; omega_using [bound, this])
    intro r mem
    simp only [WitnessChecks.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> left <;> omega_using [bound]
  have primeAt := mrLoopAt_zero (ch := P.checks) (a := P.twos.1) (m := P.twos.2) (s := P.start) v.witnessBytes
    (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact enough)
  refine ⟨⟨T, ?_, ?_, ?_, (hdr (by decide)).trans randLength,
    by simpa only [Nat.mul_zero, Nat.add_zero] using (hdr (d := 152) (by decide)).trans used,
    roundsT, uniformT, checksT, primeAt⟩, W, F, K⟩
  · rw [K.2.1, K.2.2]; exact readable
  · exact (frame_bytesAt F (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.randSeparate)
      (by have := v.randLenFit; omega_using [this])).trans entropy
  · exact (BitVec.eq_of_toNat_eq (hdr (d := 28) (by decide))).trans randPtr

theorem loopRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (.loop (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) .e) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Result P t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  let Inv : Nat → State → Prop := fun q t => ∃ i j, q = j + 1 ∧ StateAt P i j t ∧
    WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
    Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t
  have initial : Inv (n + 1) s := ⟨k, n, rfl, S, WorkspaceFrame.refl _ _ _, Frame.refl _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) Inv ?_ (n + 1) s initial
  rintro q a ⟨i, j, rfl, A, Wa, Fa, Ka⟩
  refine WP.mono (stepRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx A)
    fun t ⟨T, outcome, Wt, Ft, Kt⟩ => ?_
  rcases outcome with ⟨done, _, result⟩ | ⟨again, positive, next⟩
  · exact Or.inl ⟨done, T, result, Wa.trans Wt, Fa.trans Ft, Ka.trans Kt⟩
  · exact Or.inr ⟨again, j, by omega_using [], i + 1, j - 1, by omega_using [positive], next, Wa.trans Wt, Fa.trans Ft, Ka.trans Kt⟩

theorem codeRt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State}
    (S : Prepare.Data P.g P.candidate P.capacity P.p s)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.code montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Result P t ∧
      WorkspaceFrame P.g (MillerRabinLoop.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.code
  refine WP.seq (WP.mono (initRt_ok v Fx S readable entropy randPtr randLength used enough)
    fun a ⟨A, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (loopRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx A)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have Wsa := Wa.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ WitnessChecks.ranges, r ∈ MillerRabinLoop.ranges P.g)
  have Wat := Wt.mono (fun r mem => List.mem_append_right _ mem : ∀ r ∈ WitnessStep.ranges P.g, r ∈ MillerRabinLoop.ranges P.g)
  exact ⟨T, result, Wsa.trans Wat, (Fa.mono (fun r mem => List.mem_append_left _ mem)).trans Ft,
    (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRt
