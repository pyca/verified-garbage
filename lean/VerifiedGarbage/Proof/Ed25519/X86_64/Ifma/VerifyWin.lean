import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyAdd
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowCT

/-!
# Ed25519 verification with AVX512_IFMA: the windows in the lanes

A window of `Ifma.windows` is four doublings (`vdbl4`) and its digit's
addition (`vaddDigit`), as a window of `windows` is, with the point in the
lanes: a byte multiplies it by 256 and adds the byte's digits' multiples, as
`byteStepA_ok` and `byteStepAB_ok` show of `windows`' bytes.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1)
open VG.Proof.X25519.X86_64 (Outside off clob Keeps)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr)
open VG.Proof.Poly1305.X86_64.Avx2 (qw)

/-- A block of scalar instructions keeps the vector registers. -/
theorem WP.vk {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : is.all scalarI = true := by decide) :
    WP isa (.block is) s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  WP.vecKeep (c := .block is) hc h

/-- The constants are kept by anything that changes only bytes below them. -/
theorem EConsts.below {m m' : Mem} {base : Addr} (hk : EConsts m base) {o n : Nat}
    (h : Outside base o n m m') (hon : o + n ≤ 1664) : EConsts m' base := by
  have w : ∀ d, 1664 ≤ d → d + 8 ≤ 4096 →
      VG.Proof.X25519.X86_64.Ifma.mq m' base d = VG.Proof.X25519.X86_64.Ifma.mq m base d :=
    fun d h1 h2 => by
      rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
      exact h.word (by omega) (by omega)
  refine ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [w _ (by simp only [EK13]; omega) (by simp only [EK13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [EK26]; omega) (by simp only [EK26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [EK39]; omega) (by simp only [EK39]; omega)]; exact hk.k39 l hl

/-! ## Windows -/

theorem vwindowA_ok {s : State} {base kp sp T : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp T A s)
    (hk : EConsts s.mem base) (hx : Small s) (ha : Rep (lanePt s) a) {digit : List Instr}
    (hsc : digit.all scalarI = true) {v : Nat} (hv : v < 16) (hdig : DigitSpec base s digit v) :
    WP isa (vwindowA digit) s fun t => Rep (lanePt t) ((16 : Nat) • a + v • A) ∧ Small t ∧
      LKeep base s t := by
  rw [vwindowA]
  refine WP.seq (WP.mono (vdbl4_ok h.scratch hk hx ha) fun b ⟨bg, brd, bwr, bo, bsm, br⟩ => ?_)
  have kb : LKeep base s b := ⟨fun r _ _ hr => bg r hr, bg _ (by decide), brd, bwr, bo⟩
  refine WP.seq (WP.mono (WP.vk (hdig b kb.win) hsc) fun c ⟨⟨cv, cz, kc⟩, cx, cy⟩ => ?_)
  have kbc := kb.trans (LKeep.of_keeps kc (by decide))
  obtain ⟨pc, sc⟩ := lanePt_vec cx cy
  have hc := h.of_keep kbc.win
  refine WP.mono (vaddDigit_ok hc.scratch (kbc.consts hk) (sc bsm) (by decide) (by decide) hc.aTab v hv cv cz
    (by rw [pc]; exact br)) fun t ⟨tr, tsm, kt⟩ => ⟨tr, tsm, kbc.trans kt⟩

/-! ## Bytes -/

/-- What a byte in the lanes may change: `LKeep`'s, and the counter. -/
structure BKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  r11 : t.gpr .r11 = s.gpr .r11
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 1288 s.mem t.mem
  d : env t.mem base 16 = env s.mem base 16

theorem BKeep.refl (base : Addr) (s : State) : BKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, rfl⟩

theorem BKeep.trans {base : Addr} {s t u : State} (h : BKeep base s t) (k : BKeep base t u) :
    BKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.r11.trans h.r11, k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem, k.d.trans h.d⟩

theorem BKeep.of_lkeep {base : Addr} {s t : State} (h : LKeep base s t) : BKeep base s t :=
  ⟨h.gpr, h.r11, h.rd, h.wr, h.mem.mono (by decide) (by decide), h.slot 16⟩

theorem BKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ (r ∈ clob ∧ r ≠ .r11)) : BKeep base s t :=
  BKeep.of_lkeep (LKeep.of_keeps h hrs)

theorem BKeep.byte {base : Addr} {s t : State} (h : BKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem BKeep.consts {base : Addr} {s t : State} (h : BKeep base s t) (hk : EConsts s.mem base) :
    EConsts t.mem base := hk.below h.mem (by decide)

/-- `batchBegin`: the counter moved down, and what it keeps. -/
theorem vbatchBegin_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t => t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      BKeep base s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  WP.mono (WP.vk (batchBegin_ok hs j hc)) fun _ ⟨⟨_, av, ag, ar, aw, am⟩, ax, ay⟩ =>
    ⟨av, ⟨fun r _ hb _ => ag r hb, ag _ (by decide), ar, aw, am.mono (by decide) (by decide),
      by rw [header_env am]⟩, ax, ay⟩

theorem vbyteStepA_ok {s : State} {base kp sp T : Addr} {A : EPoint dZ} (h : WinCtx base kp sp T A s)
    (hk : EConsts s.mem base) (hx : Small s) {i : Nat} (hi32 : 32 ≤ i) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) {S : Nat} (hS : S < 256 ^ 32)
    (ha : Rep (lanePt s)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (S / 256 ^ (i + 1)) • (-baseAff))) :
    WP isa vbyteStepA s fun t => t.zf = some (decide (i = 32)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      Rep (lanePt t)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (S / 256 ^ i) • (-baseAff)) ∧ Small t ∧ BKeep base s t := by
  rw [vbyteStepA]
  refine WP.seq (WP.mono (vbatchBegin_ok h.scratch i hc) fun a ⟨av, ka, ax, ay⟩ => ?_)
  have ha' := h.of_byte ka.byte
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  have hb : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) hi, ka.byte.bytesK h]
  refine WP.seq (WP.mono (vwindowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (ka.consts hk) (sa hx) (by rw [pa]; exact ha) (by decide)
    (Nat.div_lt_of_lt_mul (by have := (a.mem (off kp i)).isLt; omega)) (digitKHigh ha' hi av))
    fun b ⟨br, bsm, kb⟩ => ?_)
  have hb' := ha'.of_keep kb.win
  refine WP.seq (WP.mono (vwindowA_ok hb' (kb.consts (ka.consts hk)) bsm br (by decide) (Nat.mod_lt _ (by decide))
    (digitKLow hb' hi (kb.win.counter.trans av))) fun c ⟨cr, csm, kc⟩ => ?_)
  have hc' := hb'.of_keep kc.win
  refine WP.mono (WP.vk (counterCmp_ok hc'.scratch i hi.le (kc.win.counter.trans (kb.win.counter.trans av))))
    fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ?_
  obtain ⟨pt, st⟩ := lanePt_vec tx ty
  refine ⟨tz, ?_, ?_, st csm, ka.trans ((BKeep.of_lkeep kb).trans ((BKeep.of_lkeep kc).trans
    (BKeep.of_keeps kt (by decide))))⟩
  · rw [kt.2.1]; exact kc.win.counter.trans (kb.win.counter.trans av)
  · rw [ha'.byteK kb.win hi] at cr
    rw [pt]
    convert cr using 1
    rw [byte_split K i _ hb, high_zero hS hi32, high_zero hS (by omega : 32 ≤ i + 1)]
    module

theorem vbyteStepAB_ok {s : State} {base kp sp T : Addr} {A : EPoint dZ} (h : WinCtx base kp sp T A s)
    (hk : EConsts s.mem base) (hx : Small s) {i : Nat} (hi : i < 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : Rep (lanePt s)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ (i + 1)) •
          (-baseAff))) :
    WP isa vbyteStepAB s fun t => t.zf = some (decide (i = 0)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      Rep (lanePt t)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ i) •
            (-baseAff)) ∧ Small t ∧ BKeep base s t := by
  rw [vbyteStepAB]
  refine WP.seq (WP.mono (vbatchBegin_ok h.scratch i hc) fun a ⟨av, ka, ax, ay⟩ => ?_)
  have ha' := h.of_byte ka.byte
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  set S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) with hSdef
  have hbK : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) (by omega), ka.byte.bytesK h]
  have hbS : (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256 := by
    rw [scalar_byte (n := 32) hi, ka.byte.bytesS h]
  have lt16 (b : Byte) : b.toNat / 16 < 16 := Nat.div_lt_of_lt_mul (by have := b.isLt; omega)
  refine WP.seq (WP.mono (vwindowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (ka.consts hk) (sa hx) (by rw [pa]; exact ha) (by decide) (lt16 _)
    (digitKHigh ha' (by omega) av)) fun b ⟨br, bsm, kb⟩ => ?_)
  have hb' := ha'.of_keep kb.win
  refine WP.seq (WP.mono (vwindowA_ok hb' (kb.consts (ka.consts hk)) bsm br (by decide)
    (Nat.mod_lt _ (by decide)) (digitKLow hb' (by omega) (kb.win.counter.trans av)))
    fun c ⟨cr, csm, kc⟩ => ?_)
  have hc' := hb'.of_keep kc.win
  have cav := kc.win.counter.trans (kb.win.counter.trans av)
  refine WP.seq (WP.mono (WP.vk (digitS_ok hc'.scratch hc'.sHeader i cav (hc'.sRead i hi)))
    fun d ⟨⟨dv, dz, kd⟩, dx, dy⟩ => ?_)
  have kd' : LKeep base c d := LKeep.of_keeps kd (by decide)
  have hd' := hc'.of_keep kd'.win
  obtain ⟨pd, sd⟩ := lanePt_vec dx dy
  have dr := cr
  rw [← pd] at dr
  refine WP.seq (WP.mono (vaddBase_ok hd'.scratch (kd'.consts ((kc.consts (kb.consts (ka.consts hk)))))
    (sd csm) hd'.bHeader hd'.bTab _ (by have := (c.mem (off (off sp 32) i)).isLt; omega) dv dz
    dr) fun e ⟨er, esm, ke⟩ => ?_)
  have he' := hd'.of_keep ke.win
  refine WP.mono (WP.vk (batchTest_ok he'.scratch i (by omega) (ke.win.counter.trans (kd'.win.counter.trans cav))))
    fun t ⟨⟨tz, kt⟩, tx, ty⟩ => ?_
  obtain ⟨pt, st⟩ := lanePt_vec tx ty
  refine ⟨tz, ?_, ?_, st esm, ka.trans ((BKeep.of_lkeep kb).trans ((BKeep.of_lkeep kc).trans
    ((BKeep.of_lkeep kd').trans ((BKeep.of_lkeep ke).trans (BKeep.of_keeps kt (by decide))))))⟩
  · rw [kt.2.1]; exact ke.win.counter.trans (kd'.win.counter.trans cav)
  · rw [ha'.byteK kb.win (by omega), ha'.byteS (kb.win.trans kc.win) hi] at er
    rw [pt]
    convert er using 1
    rw [byte_split K i _ hbK, show S / 256 ^ i = 256 * (S / 256 ^ (i + 1)) +
      (a.mem (off (off sp 32) i)).toNat by have := byte_split S i _ hbS; omega]
    module

/-! ## Loops -/

/-- The loops' invariant with the point in the lanes, with `c` bytes left: `WinLoop`'s, with
the lanes' limbs small, the constants, and what a byte keeps from `s₀`. -/
structure VLoop (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : Rep (lanePt s) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  small : Small s
  consts : EConsts s.mem base
  keep : BKeep base s₀ s

/-- A byte of `k` alone, from `32 + j + 1` bytes left to `32 + j`. -/
theorem vstepA_ok {s₀ t : State} {base kp sp T : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : VLoop s₀ base kp sp T A K S (32 + (j + 1)) t) :
    WP isa vbyteStepA t fun u => u.zf = some (decide (j = 0)) ∧ VLoop s₀ base kp sp T A K S (32 + j) u := by
  have hS : S < 256 ^ 32 := ht.sVal ▸ decodeLE_lt32 _ _
  refine WP.mono (vbyteStepA_ok (i := 32 + j) ht.ctx ht.consts ht.small (by omega) (by omega)
    (by rw [ht.counter]; rfl) hS (by rw [ht.kVal]; exact ht.value)) fun u ⟨uz, uc, uv, usm, uk⟩ => ?_
  refine ⟨by rw [uz]; simp, ht.ctx.of_byte uk.byte, by rw [uk.d]; exact ht.d, uc,
    by rw [uk.byte.bytesK ht.ctx, ht.kVal], by rw [uk.byte.bytesS ht.ctx, ht.sVal],
    by rw [ht.kVal] at uv; exact uv, usm, uk.consts ht.consts, ht.keep.trans uk⟩

/-- A byte of both scalars, from `j + 1` bytes left to `j`. -/
theorem vstepB_ok {s₀ t : State} {base kp sp T : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : VLoop s₀ base kp sp T A K S (j + 1) t) :
    WP isa vbyteStepAB t fun u => u.zf = some (decide (j = 0)) ∧ VLoop s₀ base kp sp T A K S j u := by
  refine WP.mono (vbyteStepAB_ok (i := j) ht.ctx ht.consts ht.small hj ht.counter
    (by rw [ht.kVal, ht.sVal]; exact ht.value)) fun u ⟨uz, uc, uv, usm, uk⟩ => ?_
  exact ⟨uz, ht.ctx.of_byte uk.byte, by rw [uk.d]; exact ht.d, uc, by rw [uk.byte.bytesK ht.ctx, ht.kVal],
    by rw [uk.byte.bytesS ht.ctx, ht.sVal], by rw [ht.kVal, ht.sVal] at uv; exact uv, usm,
    uk.consts ht.consts, ht.keep.trans uk⟩

theorem vloopA_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) (h : VLoop s₀ base kp sp T A K S (32 + n) s) :
    WP isa (.loop vbyteStepA .ne) s (VLoop s₀ base kp sp T A K S 32) := by
  apply WP.loop (fun (n : Nat) (t : State) => VLoop s₀ base kp sp T A K S (32 + n) t ∧ 0 < n ∧ n ≤ 32)
    (n := n)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (vstepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, hn0, hn⟩

theorem vloopB_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat}
    (h : VLoop s₀ base kp sp T A K S 32 s) :
    WP isa (.loop vbyteStepAB .ne) s (VLoop s₀ base kp sp T A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => VLoop s₀ base kp sp T A K S n t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (vstepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

theorem vwindowsA_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) (h : VLoop s₀ base kp sp T A K S c s) :
    WP isa vwindowsA s (VLoop s₀ base kp sp T A K S 32) := by
  rw [vwindowsA, counterCmp]
  refine WP.seq (WP.mono (WP.vk (counterCmp_ok h.ctx.scratch c hc64 h.counter)) fun a ⟨⟨az, ka⟩, ax, ay⟩ => ?_)
  obtain ⟨pa, sa⟩ := lanePt_vec ax ay
  have kb : BKeep base s a := BKeep.of_keeps ka (by decide)
  have ha : VLoop s₀ base kp sp T A K S c a :=
    ⟨h.ctx.of_byte kb.byte, by rw [kb.d]; exact h.d, by rw [ka.2.1]; exact h.counter,
      by rw [kb.byte.bytesK h.ctx, h.kVal], by rw [kb.byte.bytesS h.ctx, h.sVal], by rw [pa]; exact h.value,
      sa h.small, kb.consts h.consts, h.keep.trans kb⟩
  refine WP.ite (!decide (c = 32)) (by simp only [eval, az, Option.map_some]) (fun hy => ?_) (fun hy => ?_)
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    have hn : n ≠ 0 := fun h0 => by subst h0; simp at hy
    exact vloopA_ok n (by omega) (by omega) ha
  · have : c = 32 := by simpa using hy
    subst this
    exact WP.block_nil ha

/-! ## Into the lanes and back -/

/-- Before the windows: the constants, and slots 0–3 in the lanes. -/
theorem wprep_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s fun t =>
      (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 1664 224 s.mem t.mem ∧ EConsts t.mem base ∧ Small t ∧
      lanePt t = point (env s.mem base) 0 1 2 3 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.Ifma.consts_wp s)
    fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₁, m₁, rd₁, wr₁, _, _, _⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (vload_wp hs₁.rdi (ctx_of hs₁) ha hc hd hb h8 h9 h10) fun t ⟨g₂, rd₂, wr₂, o₂, k₂, u₂⟩ => ?_
  refine ⟨fun r hr => by rw [g₂, g₁ r (fun h => hr (cregs_clob r h))], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [← m₁]; exact o₂, k₂, fun l hl i hi => by have := (u₂ l hl i hi).2; omega, ?_⟩
  have e : ∀ l (hl : l < 4), fe5 (lanes t 0 l) = env s.mem base ⟨l, by omega⟩ := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_load, m₁]; rfl
  simp only [lanePt, point]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rfl

/-- The MXCSR prologue: saving it into `r11`, then `0x1FBF` into it. -/
def mxSave : List Instr := [.stmxcsr (VG.Impl.X25519.X86_64.sc EMX), .mov32 .r11 (.mem (VG.Impl.X25519.X86_64.sc EMX)),
  .alu32 .and .r11 (.imm 0xFFFF)]
def mxLoad : List Instr := [.mov32 .rax (.imm 0x1FBF), .store32 (VG.Impl.X25519.X86_64.sc (EMX + 4)) .rax,
  .ldmxcsr (VG.Impl.X25519.X86_64.sc (EMX + 4)), .lfence]
/-- The MXCSR epilogue: MXCSR back from `r11`. -/
def mxRestore : List Instr := [.store32 (VG.Impl.X25519.X86_64.sc EMX) .r11,
  .ldmxcsr (VG.Impl.X25519.X86_64.sc EMX)]

theorem withMx_eq (c : Prog isa) : withMx c =
    .seq (.block mxSave) (.seq (.seq (.block mxLoad) (.seq c (.block [.lfence]))) (.block mxRestore)) := rfl

/-- At the windows' start in the lanes, from a run of the loops started in `s₀` satisfying `R₀`:
the loops' invariant in the lanes, what has been kept since `s₀`, and `r11` the saved MXCSR,
whose reserved bits are clear. -/
def VStart (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ ByteKeep base s₀ x ∧ ((x.gpr .r11).setWidth 32).extractLsb' 16 16 = 0 ∧
    VLoop x base kp sp T A K S c x

/-- A run of the loops in the lanes, from `VStart` in `s₃`. -/
def VRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀ s₃, R₀ s₀ ∧ ByteKeep base s₀ s₃ ∧ ((s₃.gpr .r11).setWidth 32).extractLsb' 16 16 = 0 ∧
    VLoop s₃ base kp sp T A K S c x

theorem VStart.run {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat} {x : State}
    (h : VStart R₀ base kp sp T A K S c x) : VRun R₀ base kp sp T A K S c x :=
  let ⟨s₀, r₀, k, m, v⟩ := h; ⟨s₀, x, r₀, k, m, v⟩

/-- Into the lanes, and the MXCSR prologue. -/
theorem enter_ok {R₀ : State → Prop} {s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (h : LoopRun R₀ base kp sp T A K S c s) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s fun s₁ => s₁.gpr .rdi = base ∧
      WP isa (.block mxSave) s₁ fun s₂ => s₂.gpr .rdi = base ∧
        WP isa (.block mxLoad) s₂ (VStart R₀ base kp sp T A K S c) := by
  obtain ⟨s₀, r₀, h⟩ := h
  have hs := h.ctx.scratch
  refine WP.mono (wprep_ok hs) fun s₁ ⟨g₁, rd₁, wr₁, o₁, k₁, sm₁, p₁⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine ⟨hs₁.rdi, WP.mono (save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ => ?_⟩
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine ⟨hs₂.rdi, WP.mono (load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ => ?_⟩
  have q₃ : ∀ x l, qw s₃ x l = qw s₁ x l := fun x l => by rw [k₃.qw_eq, k₂.qw_eq]
  have m₃ : Outside base 56 1832 s.mem s₃.mem :=
    ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by decide) (by decide))).trans
      (k₃.mem.mono (by decide) (by decide))
  have k₀₃ : ByteKeep base s s₃ := ⟨fun r hc _ _ => by
      rw [g₃ r (fun e => hc (e ▸ by decide)), g₂ r (fun e => hc (e ▸ by decide)), g₁ r hc],
    by rw [k₃.rd, k₂.rd, rd₁], by rw [k₃.wr, k₂.wr, wr₁], m₃⟩
  have m₃' : Outside base 1600 288 s.mem s₃.mem :=
    ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by simp only [EMX]; omega) (by simp only [EMX]; omega))).trans
      (k₃.mem.mono (by simp only [EMX]; omega) (by simp only [EMX]; omega))
  refine ⟨s₀, r₀, h.keep.trans k₀₃, by rw [g₃ _ (by decide), r11₂]; exact and_ffff _, ?_⟩
  refine ⟨h.ctx.of_byte k₀₃, ?_, ?_, by rw [k₀₃.bytesK h.ctx, h.kVal], by rw [k₀₃.bytesS h.ctx, h.sVal],
    ?_, fun l hl i hi => by rw [lanes_qw q₃]; exact sm₁ l hl i hi, (k₁.outsideMx k₂.mem).outsideMx k₃.mem,
    BKeep.refl _ _⟩
  · rw [show env s₃.mem base 16 = env s.mem base 16 from
      Outside_F m₃' (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))]
    exact h.d
  · exact (m₃'.word (Or.inl (by decide)) (by decide)).trans h.counter
  · rw [lanePt_qw q₃, p₁]; exact h.value

/-- Back into slots 0–3, and the MXCSR epilogue. -/
theorem exit_ok {R₀ : State → Prop} {w : State} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat}
    (h : VRun R₀ base kp sp T A K S 0 w) :
    WP isa (.block vstore) w fun t₀ => t₀.gpr .rdi = base ∧
      WP isa (.block [.lfence]) t₀ fun t₁ => t₁.gpr .rdi = base ∧
        WP isa (.block mxRestore) t₁ (LoopRun R₀ base kp sp T A K S 0) := by
  obtain ⟨s₀, s₃, r₀, k₀₃, m₃, hw⟩ := h
  have hsw : Scratch w base := hw.ctx.scratch
  refine WP.mono (vstore_wp hsw.rdi (ctx_of hsw) hw.consts hw.small) fun t₀ ⟨tg, trd, twr, tou, tf⟩ => ?_
  have hs₀ : Scratch t₀ base := ⟨by rw [tg]; exact hsw.rdi, by rw [twr]; exact hsw.wr, hsw.nowrap⟩
  refine ⟨hs₀.rdi, WP.mono (lfence_wp t₀) fun t₁ e₁ => ?_⟩
  subst e₁
  refine ⟨hs₀.rdi, ?_⟩
  refine WP.mono (restore_wp hs₀ (by rw [tg, hw.keep.r11]; exact m₃)) fun t ⟨g₈, k₈⟩ => ?_
  have pt : point (env t.mem base) 0 1 2 3 = lanePt w := by
    simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
    rw [← tf 0 (by decide), ← tf 1 (by decide), ← tf 2 (by decide), ← tf 3 (by decide),
      Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide)),
      Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide))]
    rfl
  have mwt : Outside base 64 1544 w.mem t.mem :=
    (tou.mono (by decide) (by decide)).trans (k₈.mem.mono (by simp only [EMX]; omega) (by simp only [EMX]; omega))
  have kwt : ByteKeep base w t := ⟨fun r _ _ _ => by rw [g₈, tg], by rw [k₈.rd, trd], by rw [k₈.wr, twr],
    mwt.mono (by decide) (by decide)⟩
  have kst : ByteKeep base s₃ t := hw.keep.byte.trans kwt
  refine ⟨s₀, r₀, hw.ctx.of_byte kwt, ?_, ?_, by rw [kwt.bytesK hw.ctx, hw.kVal],
    by rw [kwt.bytesS hw.ctx, hw.sVal], by rw [pt]; exact hw.value, k₀₃.trans kst⟩
  · rw [show env t.mem base 16 = env t₁.mem base 16 from
        Outside_F k₈.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset, EMX]; omega)),
      show env t₁.mem base 16 = env w.mem base 16 from
        Outside_F tou (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))]
    exact hw.d
  · exact (mwt.word (Or.inl (by decide)) (by decide)).trans hw.counter

/-- `Ifma.windows` keeps the loops' invariant, from `c` bytes left to none. -/
theorem windows_ok {R₀ : State → Prop} {s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) (h : LoopRun R₀ base kp sp T A K S c s) :
    WP isa Impl.Ed25519.X86_64.Ifma.windows s (LoopRun R₀ base kp sp T A K S 0) := by
  rw [Impl.Ed25519.X86_64.Ifma.windows, withMx_eq]
  refine WP.seq (WP.mono (enter_ok h) fun s₁ ⟨_, h₁⟩ => WP.seq (WP.mono h₁ fun s₂ ⟨_, h₂⟩ => ?_))
  refine WP.seq (WP.seq (WP.mono h₂ fun s₃ h₃ => ?_))
  obtain ⟨s₀, r₀, k₀, m₀, v₃⟩ := h₃
  refine WP.seq (WP.seq (WP.mono (vwindowsA_ok hc32 hc64 v₃) fun f hf => ?_))
  refine WP.seq (WP.mono (vloopB_ok hf) fun w hw => ?_)
  exact WP.mono (exit_ok ⟨s₀, s₃, r₀, k₀, m₀, hw⟩) fun _ ⟨_, h₄⟩ => WP.mono h₄ fun _ ⟨_, h₅⟩ => h₅

end VG.Proof.Ed25519.X86_64.Ifma
