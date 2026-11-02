module

import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.RsaKeyGen.X86.OrLoopRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallbackWord
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32
import VerifiedGarbage.Proof.RsaKeyGen.WitnessSample
import VerifiedGarbage.Proof.Mont.LowUpdate32
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.MillerRabin.Contract

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
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega)) fun b B _ => wp_movS rfl fun c Cc _ =>
    wp_orS rfl fun d D => ?_
  have Kd : Keeps [.eax, .ebx] s d := ((B.keeps.mono (by decide)).widen Cc.keeps).widen D.keeps
  have wd := hw.of_keeps Kd
  have Pd : PtrAt d W .ebp x := by rw [PtrAt, Kd.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr wd Pd (d := 0) (by omega)) (ws_write wd (y := x + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have Mt : t.mem = s.mem.writeW (off W x) (d.gpr .eax) := by
    rw [T.mem, D.mem, Cc.mem, B.mem, Nat.add_zero]
  have O : Outside W x 4 s.mem t.mem := by
    rw [Mt]; exact writeW32_outside _ _ _ (by omega)
  have low : w32 t.mem W x = w32 s.mem W x ||| 1 := by
    rw [Mt, w32_write_self, D.gpr, Cc.gpr, B.gpr, Nat.add_zero, BitVec.toNat_or]
    rfl
  refine ⟨val32_low_or_one positive (by omega) O low, ?_, O, Kd.widen (T.keeps [])⟩
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
  refine WP.mono (markAt_ok (C.ws.of_keeps K) P (n := g.words) (by omega) fit) fun t ⟨V, E, O, Kt⟩ => ?_
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
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (Ca.ptr v 0 (by decide) .ebp (by decide) (by decide)) fun b ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Ca.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (draw_ok v Cb) fun c ⟨D, Mc, Kc⟩ => ?_)
  refine wp_movS rfl fun d Dd _ => WP.block_nil ⟨?_, ?_, ?_, Dd.gpr, by rw [Dd.mem, Mc, Mb, Ma],
    (((Ka.mono (by decide)).widen Kb).widen Kc).widen Dd.keeps⟩
  · rw [PtrAt, Dd.other .esi (by decide), Kc.1 .esi (by decide), Kb.1 .esi (by decide)]; exact Pa
  · rw [PtrAt, Dd.other .ebp (by decide), Kc.1 .ebp (by decide)]; exact Pb
  · rw [Dd.other .edx (by decide), D, BitVec.toNat_ofNat]; omega

theorem less_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa less s fun t =>
      t.gpr .ecx = cmask (decide (val32 s.mem g.W (g.array 6) g.words < val32 s.mem g.W (g.array 0) g.words)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  obtain ⟨fit, below, many, words⟩ := fits v
  unfold less
  refine WP.seq (WP.mono (lessArgs_ok v C) fun d ⟨esi, ebp, edx, ecx, Md, K⟩ => ?_)
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.compareLoop_ok (C.ws.of_keeps K) (x := g.array 6) (y := g.array 0)
    (N := g.words) (by omega) (by omega) (by omega) esi ebp edx ecx) fun t ⟨Mt, E, Kt⟩ => ?_
  rw [Md] at Mt E
  exact ⟨E, Mt, (K.mono (by decide)).trans Kt⟩

theorem restoreAt_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 4 ≤ L) :
    WP isa (.block restoreAt) s fun t =>
      w32 t.mem W x = (s.gpr .ebx).toNat ∧ Outside W x 4 s.mem t.mem ∧ t.gpr .esi = s.gpr .ecx ∧
      Keeps [.esi] s t := by
  have nowrap := hw.nowrap
  unfold restoreAt
  refine wp_storeS (ea_ptr hw P (d := 0) (by omega)) (ws_write hw (y := x + 0) (n := 4) (by omega))
    fun b B => wp_movS rfl fun t T _ => WP.block_nil ?_
  have Mt : t.mem = s.mem.writeW (off W x) (s.gpr .ebx) := by rw [T.mem, B.mem, Nat.add_zero]
  refine ⟨by rw [Mt, w32_write_self], by rw [Mt]; exact writeW32_outside _ _ _ (by omega), ?_,
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
  refine WP.mono (restoreAt_ok (C.ws.of_keeps K) P (by omega)) fun t ⟨low, Ot, E, Kt⟩ => ?_
  rw [M] at Ot
  have low' : w32 t.mem g.W (g.array 6) = w32 original.mem g.W (g.array 6) := by
    rw [low, K.1 .ebx (by decide), saved]
  refine ⟨val32_restore_low (by omega) (by omega) (O.trans Ot) low', O.trans Ot, ?_, (K.mono (by decide)).widen Kt⟩
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
  have Ca := C.keepMem A.keeps (by decide) A.mem
  refine WP.block_append (WP.mono (Ca.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun b ⟨P, Mb, Kb⟩ => ?_)
  refine wp_addS rfl fun c Cc _ => ?_
  have Kc : Keeps [.ebx, .ebp, .edx] s c := ((A.keeps.mono (by decide)).widen Kb).widen Cc.keeps
  refine wp_movS (readSrc_ptr (C.ws.of_keeps Kc) (r := .edi) (x := 0) (d := 48)
    (by rw [PtrAt, Kc.1 .edi (by decide)]; exact C.base) (by omega)) fun d Dd _ =>
    wp_addS rfl fun e E _ => wp_subS rfl fun f F _ => WP.block_nil ?_
  have width : (d.gpr .ecx).toNat = g.w := by
    rw [Dd.gpr, Cc.mem, Mb, A.mem]; exact C.width
  refine ⟨?_, ?_, ?_, by rw [F.mem, E.mem, Dd.mem, Cc.mem, Mb, A.mem],
    (((Kc.mono (by decide)).widen Dd.keeps).widen E.keeps).widen F.keeps⟩
  · rw [PtrAt, F.other .ebp (by decide), E.other .ebp (by decide), Dd.other .ebp (by decide), Cc.gpr]
    exact ptr_add P 4
  · rw [F.gpr, E.gpr, BitVec.toNat_sub_of_le, BitVec.toNat_add, width]
    · change (g.w + g.w) % 2 ^ 32 - 1 = g.words - 1
      omega
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
  refine WP.mono (FrontRt.orLoop_ok (C.ws.of_keeps Kf) (by omega) (by omega) Pf count zero) fun t ⟨Z, Mt, _, Kt⟩ => ?_
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
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega)) fun b0 B _ => wp_orS rfl fun c Cc =>
    wp_logicS (.inr rfl) rfl fun d D => wp_orS rfl fun e E => ?_
  have low : d.gpr .eax = (s.mem.readW (off W x) 32 ||| 1#32) ^^^ 1#32 := by
    rw [D.gpr, Cc.gpr, B.gpr, Nat.add_zero]
    rfl
  have combined : e.gpr .ebx = s.gpr .ebx ||| ((s.mem.readW (off W x) 32 ||| 1#32) ^^^ 1#32) := by
    rw [E.gpr, low, D.other .ebx (by decide), Cc.other .ebx (by decide), B.other .ebx (by decide)]
  have combinedZero : (e.gpr .ebx).toNat = 0 ↔ ¬ 2 ≤ val32 s.mem W x n := by
    rw [show (e.gpr .ebx).toNat = 0 ↔ e.gpr .ebx = 0#32 from @BitVec.toNat_inj 32 (e.gpr .ebx) (0#32),
      combined, BitVec.or_eq_zero_iff, zero, WitnessLower.clear_low_zero, Nat.not_le,
      WitnessLower.below_two _ _ _ _ positive]
  refine wp_cmpi fun f F cf _ => wp_sbb_self cf fun h H => wp_logicS (.inr rfl) rfl fun i I =>
    wp_movS rfl fun j J _ => wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  have Ki : Keeps [.eax, .ebx] s i :=
    ((((((B.keeps.mono (by decide)).widen Cc.keeps).widen D.keeps).widen E.keeps).trans
      (F.keeps _)).widen H.keeps).widen I.keeps
  have ebx : i.gpr .ebx = cmask (decide (2 ≤ val32 s.mem W x n)) := by
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
  refine WP.mono (lowerAt_ok (b := b) (C.ws.of_keeps K) P (n := g.words) (by omega) fit
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
  have Kc : Keeps [.ecx] s c := (A.keeps.widen B.keeps).widen C.keeps
  have Pc : PtrAt c W .ebp x := by rw [PtrAt, Kc.1 .ebp (by decide)]; exact P
  have load := readSrc_ptr (hw.of_keeps Kc) Pc (d := 0) (by omega)
  rw [C.mem, B.mem, A.mem, Nat.add_zero] at load
  refine wp_orS load fun d D => ?_
  have Kd : Keeps [.ecx] s d := Kc.widen D.keeps
  have wd := hw.of_keeps Kd
  have Pd : PtrAt d W .ebp x := by rw [PtrAt, Kd.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr wd Pd (d := 0) (by omega)) (ws_write wd (y := x + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have V : d.gpr .ecx = (((cmask uniform ^^^ BitVec.allOnes 32) &&& 2#32) ||| s.mem.readW (off W x) 32) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Kd.widen (T.keeps [])⟩
  · rw [T.mem, Nat.add_zero, w32_write_self, V]
    exact WitnessFallback.low_value _ _
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

theorem fallbackHigh_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebx x)
    (fit : x + 4 ≤ L) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block fallbackHigh) s fun t =>
      w32 t.mem W x = (if uniform then w32 s.mem W x else w32 s.mem W x % 2 ^ 31) ∧
      Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackHigh
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B =>
    wp_logicS (.inl rfl) rfl fun c C => wp_logicS (.inr rfl) rfl fun d D => ?_
  have Kd : Keeps [.ecx] s d := ((A.keeps.widen B.keeps).widen C.keeps).widen D.keeps
  have Pd : PtrAt d W .ebx x := by rw [PtrAt, Kd.1 .ebx (by decide)]; exact P
  have load := readSrc_ptr (hw.of_keeps Kd) Pd (d := 0) (by omega)
  rw [D.mem, C.mem, B.mem, A.mem, Nat.add_zero] at load
  refine wp_logicS (.inl rfl) load fun e E => ?_
  have Ke : Keeps [.ecx] s e := Kd.widen E.keeps
  have we := hw.of_keeps Ke
  have Pe : PtrAt e W .ebx x := by rw [PtrAt, Ke.1 .ebx (by decide)]; exact P
  refine wp_storeS (ea_ptr we Pe (d := 0) (by omega)) (ws_write we (y := x + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have V : e.gpr .ecx = ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 0x80000000#32) ^^^
      BitVec.allOnes 32) &&& s.mem.readW (off W x) 32) := by
    rw [E.gpr, D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Ke.widen (T.keeps [])⟩
  · rw [T.mem, Nat.add_zero, w32_write_self, V]
    exact WitnessFallback.high_value _ _
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

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
  have ebp : (c.gpr .ebp).toNat = (g.W.toNat + g.array 6) % 2 ^ 32 := by
    rw [Kc.1 .ebp (by decide)]; exact P
  have sum : PtrAt e g.W .ebx (g.array 6 + 4 * g.words) := by
    rw [PtrAt, E.gpr, Dd.gpr, Dd.other .edx (by decide), ptr_add ebp, D, BitVec.toNat_ofNat]
    congr 2
    omega
  refine ⟨?_, by rw [F.mem, E.mem, Dd.mem, Mc], (((Kc.mono (by decide)).widen Dd.keeps).widen E.keeps).widen F.keeps⟩
  rw [PtrAt, F.gpr, ptr_sub sum 4 (by change 4 ≤ _; omega)]
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
  have header := v.arrayHeader 6
  unfold fallback
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (C.ptr v 6 (by decide) .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_)
  have Ca := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (fallbackLow_ok (uniform := uniform) Ca.ws P (by omega) (by rw [K.1 .eax (by decide)]; exact mask))
    fun b ⟨low, Ob, Kb⟩ => ?_)
  have Cb := Ca.keepOutside Kb (by decide) Ob header
  refine WP.block_append (WP.mono (fallbackTop_ok v Cb (by rw [PtrAt, Kb.1 .ebp (by decide)]; exact P))
    fun f ⟨Pf, Mf, Kcf⟩ => ?_)
  have Kf : Keeps [.ebx, .ecx, .ebp, .edx] s f := (((K.mono (by decide)).widen Kb).widen Kcf)
  refine WP.mono (fallbackHigh_ok (uniform := uniform) (Cb.ws.of_keeps Kcf)
    Pf (by omega) (by
      rw [Kcf.1 .eax (by decide), Kb.1 .eax (by decide), K.1 .eax (by decide)]
      exact mask)) fun t ⟨top, Ot, Kt⟩ => ?_
  rw [Mf] at top Ot
  rw [M] at low Ob
  have lowSame : w32 t.mem g.W (g.array 6) = w32 b.mem g.W (g.array 6) := Ot.w32 (by omega) (by omega)
  have topSame : w32 b.mem g.W (g.array 6 + 4 * g.words - 4) = w32 s.mem g.W (g.array 6 + 4 * g.words - 4) :=
    Ob.w32 (by omega) (by omega)
  refine ⟨?_, (Ob.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), Kf.widen Kt⟩
  cases uniform
  · simp only [Bool.false_eq_true, ↓reduceIte] at low top ⊢
    apply VG.Proof.RsaKeyGen.val32_witness_fallback (by omega)
    · rw [lowSame, low]
    · rw [show g.array 6 + 4 * (g.words - 1) = g.array 6 + 4 * g.words - 4 by omega, top, topSame]
    · intro j first last
      exact (Ot.w32 (by omega) (by omega)).trans (Ob.w32 (by omega) (by omega))
  · simp only [↓reduceIte] at low top ⊢
    apply val32_congr
    intro j hj
    by_cases first : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using lowSame.trans low
    · by_cases last : j = g.words - 1
      · subst j
        rw [show g.array 6 + 4 * (g.words - 1) = g.array 6 + 4 * g.words - 4 by omega]
        exact top.trans topSame
      · exact (Ot.w32 (by omega) (by omega)).trans (Ob.w32 (by omega) (by omega))

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
  have header := v.arrayHeader 6
  have bound : x < 2 ^ (32 * g.words) := witness ▸ val32_lt s.mem g.W (g.array 6) g.words
  have sampled := VG.Proof.RsaKeyGen.witness_sampleAt shape bound
  unfold sample
  refine WP.seq (WP.mono (mark_ok v C) fun a ⟨Va, saved, Oa, Ka⟩ => ?_)
  rw [witness] at Va
  have Ca := C.keepOutside Ka (by decide) Oa header
  refine WP.seq (WP.mono (less_ok v Ca) fun b ⟨lt, Mb, Kb⟩ => ?_)
  have Cb := Ca.keepMem Kb (by decide) Mb
  have modA : val32 a.mem g.W (g.array 0) g.words = c := by
    rw [Oa.val32 (by omega) (by omega)]; exact candidate
  rw [Va, modA] at lt
  refine WP.seq (WP.mono (restore_ok (original := s) v Cb (by rw [Mb]; exact Oa)
    (by rw [Kb.1 .ebx (by decide)]; exact saved)) fun d ⟨Vd, Od, esi, Kd⟩ => ?_)
  rw [witness] at Vd
  have Kad : Keeps clob s d := (((Ka.mono (by unfold clob; decide)).widen Kb (by unfold clob; decide)).widen Kd
    (by unfold clob; decide))
  have Cd := C.keepOutside Kad (by unfold clob; decide) Od header
  refine WP.seq (WP.mono (scan_ok v Cd) fun e ⟨Z, Me, Ke⟩ => ?_)
  rw [← Me] at Z
  have Ce := Cd.keepMem Ke (by decide) Me
  refine WP.block_append (WP.mono (lower_ok v Ce Z (b := decide (x + (1 - x % 2) < c))
    (by rw [Ke.1 .esi (by decide), esi, lt])) fun f ⟨eax, Mf, Kf⟩ => ?_)
  have Cf := Ce.keepMem Kf (by decide) Mf
  have Ve : val32 e.mem g.W (g.array 6) g.words = x := by rw [Me]; exact Vd
  have uniform : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = decide (2 ≤ x ∧ x < c - 1) := by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr (by omega)
  rw [Ve, uniform] at eax
  refine WP.mono (fallback_ok v Cf eax) fun t ⟨V, Ot, Kt⟩ => ?_
  rw [Mf, Ve] at V
  rw [Mf, Me] at Ot
  have O : Outside g.W (g.array 6) (4 * g.words) s.mem t.mem := (Od.mono (by omega) (by omega)).trans Ot
  have K : Keeps clob s t := ((Kad.widen Ke (by unfold clob; decide)).widen Kf (by unfold clob; decide)).widen Kt
    (by unfold clob; decide)
  refine ⟨?_, ?_, O, K, C.keepOutside K (by unfold clob; decide) O header⟩
  · rw [sampled]; exact V
  · rw [Kt.1 .eax (by decide), eax, sampled]

end VG.Proof.RsaKeyGen.X86.WitnessRt
