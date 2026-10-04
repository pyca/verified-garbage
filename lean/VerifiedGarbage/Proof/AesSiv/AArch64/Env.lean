import VerifiedGarbage.Proof.AesSiv.AArch64.Init
import VerifiedGarbage.Proof.CmacAes.AArch64.Finalize
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Finish
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# AES-SIV on AArch64: the regions of `encrypt` and `decrypt`

The functions' S2V and CTR work on the key context `C`, the rounds `R`, `D`
(16 bytes, at `W + 2560`), a string `P` (`L` bytes: a component of
associated data, or the data) and the working space `W` (2560 bytes). They
call `vg_cmac_aes_update` and `vg_cmac_aes_finalize` with the context as the
key, a CMAC state in the working space, the string or the working space as
the message, and the working space at `W + 256` as theirs (`Env.uargs`,
`Env.fargs`); and `vg_aes_ctr32` with `K2`'s schedule and blocks of the
working space (`Env.cargs`). `Env` names what their contracts say about the
regions, whichever of them are writable; `Regs` the registers that hold the
arguments while the code runs.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.CmacAes.Stream.AArch64 (UArgs FArgs toNat_add_lt)
open VG.Proof.CmacAes.AArch64 (CallPre k0)

/-- The regions of the arguments. -/
structure Env (s₀ : State) (C D P W : Addr) (R L : Nat) : Prop where
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hD : D = W + BitVec.ofNat 64 dOff
  ctxIn : (⟨C, 512⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dIn : (⟨D, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dataIn : (⟨P, L⟩ : Region) ∈ s₀.rd ++ s₀.wr
  workIn : (⟨W, 2560⟩ : Region) ∈ s₀.wr
  c_w : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2560⟩
  d_p : (⟨D, 16⟩ : Region).Disjoint ⟨P, L⟩
  d_w : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  p_w : (⟨P, L⟩ : Region).Disjoint ⟨W, 2560⟩
  wC : C.toNat + 512 ≤ 2 ^ 64
  wD : D.toNat + 16 ≤ 2 ^ 64
  wP : P.toNat + L ≤ 2 ^ 64
  wW : W.toNat + 2560 ≤ 2 ^ 64
  lt : L < 2 ^ 64

/-- The registers that hold the arguments while the code runs: the working
space in `x19`, the context in `x20`, the rounds in `x21`, and the string in
`x22` (`x23` bytes). -/
structure Regs (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x22 : s.gpr .x22 = P
  x23 : s.gpr .x23 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Regs.keep {s₀ s s' : State} {C D P W : Addr} {R L : Nat} (h : Regs s₀ C D P W R L s)
    (hs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Regs s₀ C D P W R L s' :=
  ⟨by rw [hs _ (by decide) (by decide), h.x19], by rw [hs _ (by decide) (by decide), h.x20],
    by rw [hs _ (by decide) (by decide), h.x21], by rw [hs _ (by decide) (by decide), h.x22],
    by rw [hs _ (by decide) (by decide), h.x23], by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

/-- A property every register of a literal list has, for a register of it. -/
theorem dec_mem {l : List Reg} {p : Reg → Prop} [DecidablePred p] (h : l.all (fun r => decide (p r)) = true)
    {r : Reg} (hr : r ∈ l) : p r :=
  of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- A register of a literal list without `x`. -/
theorem dec_ne {l : List Reg} {x : Reg} (h : l.contains x = false) {r : Reg} (hr : r ∈ l) : r ≠ x := by
  rintro rfl; simp_all

/-- `Regs.keep` after code that writes none of `x19`–`x23`. -/
theorem Regs.keep' {s₀ s s' : State} {C D P W : Addr} {R L : Nat} (h : Regs s₀ C D P W R L s)
    (hs : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Regs s₀ C D P W R L s' :=
  ⟨by rw [hs _ (by decide), h.x19], by rw [hs _ (by decide), h.x20], by rw [hs _ (by decide), h.x21],
    by rw [hs _ (by decide), h.x22], by rw [hs _ (by decide), h.x23], by rw [hsp, h.sp], by rw [hrd, h.rd],
    by rw [hwr, h.wr]⟩

/-- A region at an offset of one of `rs`. -/
theorem cov_off {rs : List Region} {r : Region} (hr : r ∈ rs) {off n : Nat} (h : off + n ≤ r.len) :
    Covers [⟨r.base + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨r, hr, off, rfl, h⟩

theorem cov_base {rs : List Region} {r : Region} (hr : r ∈ rs) {n : Nat} (h : n ≤ r.len) :
    Covers [⟨r.base, n⟩] rs := by
  have := cov_off hr (off := 0) (n := n) (by omega)
  rwa [k0] at this

/-- The PRF and the cipher of a key context outside a frame's regions. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.Cmac.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.Cmac.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

/-- The registers the taint analysis needs public around the calls. -/
theorem regs_agree {s₀ s₀' a b : State} {C D P W : Addr} {R L : Nat} (hq : s₀.sp = s₀'.sp)
    (ha : Regs s₀ C D P W R L a) (hb : Regs s₀' C D P W R L b) :
    taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) a b := by
  refine Proof.CmacAes.AArch64.agree_of (by rw [ha.sp, hb.sp, hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [ha.x19, hb.x19]
  · rw [ha.x20, hb.x20]
  · rw [ha.x21, hb.x21]
  · rw [ha.x22, hb.x22]
  · rw [ha.x23, hb.x23]

/-- `xor2` is the block XOR of the CMAC proofs. -/
theorem xor2_eq (pb qb cb : Reg) (pd qd cd : Nat) :
    xor2 pb qb cb pd qd cd = Proof.CmacAes.AArch64.xor2 pb qb cb pd qd cd := rfl

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

theorem z0 : BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0 := by decide

/-- `copy16 src dst`: the block at `B + src` copied to `B + dst`, a word at a time. -/
theorem copy16_ok {s : State} {B : Addr} (hb : s.gpr .x19 = B) {src dst : Nat}
    (hs : src % 8 = 0 ∧ src + 8 < 32768) (hd : dst % 8 = 0 ∧ dst + 8 < 32768)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (B + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (B + BitVec.ofNat 64 (dst + 8)) 8) :
    ∃ s', runBlock isa (copy16 src dst) s = some s' ∧
      s'.mem = Proof.CmacAes.Stream.AArch64.copyMem s.mem (B + BitVec.ofNat 64 dst) (B + BitVec.ofNat 64 src) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, and_self, copy16, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write,
      Option.bind_some, Option.map_some, hb, hs.1, hd.1, BitVec.setWidth_eq,
      show src < 32768 by omega, show src + 8 < 32768 from hs.2, show dst < 32768 by omega,
      show dst + 8 < 32768 from hd.2, Nat.add_mod_right, r₀, r₁, w₀, w₁, and_self]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ => by simp [gpr_write, h₁], rfl, rfl, rfl⟩
  simp only [Proof.CmacAes.Stream.AArch64.copyMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, Offset.add_add]

namespace Env

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem sW (_h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base W hd

theorem sC (_h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 512) :
    Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base C hd

theorem sP (_h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ L) :
    Region.Sub ⟨P + BitVec.ofNat 64 d, n⟩ ⟨P, L⟩ :=
  Offset.sub_base P hd

theorem inW (h : Env s₀ C D P W R L) {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ 2560) :
    InRegions s.wr (W + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, h.workIn, Offset.contains_base W hd (by have := h.wW; omega)⟩

theorem inRW (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]
  obtain ⟨r, hr, hc⟩ := h.inW (s := s₀) rfl hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inRC (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.ctxIn, Offset.contains_base C hd (by have := h.wC; omega)⟩

theorem inRP (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ L) : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dataIn, Offset.contains_base P hd (by have := h.wP; have := h.lt; omega)⟩

theorem inWP (h : Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hwr : s.wr = s₀.wr)
    {d n : Nat} (hd : d + n ≤ L) : InRegions s.wr (P + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, hPw, Offset.contains_base P hd (by have := h.wP; have := h.lt; omega)⟩

theorem inRD (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dIn, Offset.contains_base D hd (by have := h.wD; omega)⟩

/-- A message for the CMAC functions: `n` bytes at `Q`, which miss the state at
`W + o` and the working space of the functions called. -/
structure Src (s₀ : State) (W : Addr) (o : Nat) (Q : Addr) (n : Nat) : Prop where
  qo : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩
  qs : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩
  wrap : Q.toNat + n ≤ 2 ^ 64
  cov : Covers [⟨Q, n⟩] (s₀.rd ++ s₀.wr)

/-- Data bytes as the message. -/
theorem srcData (h : Env s₀ C D P W R L) {o a n : Nat} (ho : o + 16 ≤ 2560) (ha : a + n ≤ L) :
    Src s₀ W o (P + BitVec.ofNat 64 a) n where
  qo := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW ho)
  qs := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW (by decide))
  wrap := by
    have := h.wP
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := (P + BitVec.ofNat 64 a).isLt; omega
    · rw [toNat_add_lt P this (by omega)]; omega
  cov := cov_off h.dataIn ha

theorem srcData₀ (h : Env s₀ C D P W R L) {o n : Nat} (ho : o + 16 ≤ 2560) (hn : n ≤ L) :
    Src s₀ W o P n := by
  have := h.srcData (o := o) (a := 0) (n := n) ho (by omega)
  rwa [k0] at this

/-- Bytes of the working space below `W + 256`, apart from the state, as the message. -/
theorem srcWork (h : Env s₀ C D P W R L) {o t n : Nat} (ho : o + 16 ≤ 256) (ht : t + n ≤ 256)
    (hs : t + n ≤ o ∨ o + 16 ≤ t) : Src s₀ W o (W + BitVec.ofNat 64 t) n where
  qo := Offset.disjoint W hs (by omega) (by omega)
  qs := Offset.disjoint W (by omega) (by omega) (by omega)
  wrap := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  cov := Covers.right (cov_off h.workIn (by simp; omega))

/-- The arguments of `vg_cmac_aes_finalize`: the context as the key, the
state at `St` (in the working space below `W + 256`, or `D`), the message at
`Q`, and the working space at `W + 256`. -/
theorem fargs' (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {St : Addr} (hSt : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩)
    (hcs : (⟨C, 512⟩ : Region).Disjoint ⟨St, 16⟩) (hwSt : St.toNat + 16 ≤ 2 ^ 64)
    (hcov : Covers [⟨St, 16⟩] s₀.wr) {Q : Addr} {n : Nat}
    (hq : (⟨Q, n⟩ : Region).Disjoint ⟨St, 16⟩) (hqs : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩)
    (hqw : Q.toNat + n ≤ 2 ^ 64) (hqc : Covers [⟨Q, n⟩] (s₀.rd ++ s₀.wr)) (hn : n ≤ 16)
    (x0 : s.gpr .x0 = C) (x1 : s.gpr .x1 = BitVec.ofNat 64 R) (x2 : s.gpr .x2 = St)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 n) (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256) :
    FArgs s C St Q (W + BitVec.ofNat 64 256) n R where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := h.rounds
  len := hn
  kst := hcs.sub_left (Region.sub_prefix (by decide))
  ks := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  pst := hq
  ps := hqs
  sts := hSt
  wrapK := by have := h.wC; omega
  wrapSt := hwSt
  wrapP := hqw
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    exact Covers.append_left (Covers.cons (cov_base h.ctxIn (by simp)) (Covers.cons hqc Covers.nil))
      (Covers.cons (Covers.right hcov) (Covers.cons (Covers.right (cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons hcov (Covers.cons (cov_off h.workIn (by simp)) Covers.nil)

/-- `fargs'` with the state at `W + o`. -/
theorem fargs (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : Src s₀ W o Q n) (hn : n ≤ 16)
    (x0 : s.gpr .x0 = C) (x1 : s.gpr .x1 = BitVec.ofNat 64 R) (x2 : s.gpr .x2 = W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 n) (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256) :
    FArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) n R :=
  h.fargs' hrd hwr (Offset.disjoint W (by omega) (by omega) (by omega))
    ((h.c_w.sub_right (h.sW (by omega))))
    (by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega) (cov_off h.workIn (by simp; omega))
    hq.qo hq.qs hq.wrap hq.cov hn x0 x1 x2 x3 x4 x5

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + o`, `n` blocks at `Q`, and the working space at `W + 256`. -/
theorem uargs (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : Src s₀ W o Q (16 * n)) (hn : 16 * n < 2 ^ 64)
    (x0 : s.gpr .x0 = C) (x1 : s.gpr .x1 = BitVec.ofNat 64 R) (x2 : s.gpr .x2 = W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 n) (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256) :
    UArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) R n where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := h.rounds
  hn := hn
  wc := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by omega))
  ws := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  dc := hq.qo
  ds := hq.qs
  cs := Offset.disjoint W (by omega) (by omega) (by omega)
  wrapC := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  wrapD := hq.wrap
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    exact Covers.append_left (Covers.cons (cov_base h.ctxIn (by simp)) (Covers.cons hq.cov Covers.nil))
      (Covers.cons (Covers.right (cov_off h.workIn (by simp; omega)))
        (Covers.cons (Covers.right (cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_off h.workIn (by simp; omega)) (Covers.cons (cov_off h.workIn (by simp)) Covers.nil)

/-- The arguments of `vg_aes_ctr32` on one block: `K2`'s schedule, the counter
block at `W + 96`, the keystream block at `W + 80` (zero), and the working
space at `W + 256`. -/
theorem cargs (h : Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (x0 : s.gpr .x0 = C + BitVec.ofNat 64 272) (x1 : s.gpr .x1 = BitVec.ofNat 64 R)
    (x2 : s.gpr .x2 = W + BitVec.ofNat 64 96) (x3 : s.gpr .x3 = W + BitVec.ofNat 64 80) (x4 : s.gpr .x4 = 1)
    (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256)
    (hz : Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16) :
    CallPre s (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256)
      R where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := h.rounds
  wc := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  wd := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  ws := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  cd := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  cs := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  ds := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  wrap := by rw [toNat_add_lt W h.wW (show 80 < 2560 by decide)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (cov_off h.ctxIn (by simp)) Covers.nil)
      (Covers.cons (Covers.right (cov_off h.workIn (by simp)))
        (Covers.cons (Covers.right (cov_off h.workIn (by simp)))
          (Covers.cons (Covers.right (cov_off h.workIn (by simp))) Covers.nil)))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_off h.workIn (by simp)) (Covers.cons (cov_off h.workIn (by simp))
      (Covers.cons (cov_off h.workIn (by simp)) Covers.nil))
  zero := hz

/-- The 16 bytes at `W + d` zeroed. -/
theorem zero16_ok (h : Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hwr : s.wr = s₀.wr) {d : Nat}
    (hd : d + 16 ≤ 2560) (h8 : d % 8 = 0) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 d) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₀ := h.inW hwr (d := d) (n := 8) (by omega)
  have w₁ := h.inW hwr (d := d + 8) (n := 8) (by omega)
  have h8' : (d + 8) % 8 = 0 := by omega
  have l₀ : d < 32768 := by omega
  have l₁ : d + 8 < 32768 := by omega
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, and_self, zero16, runBlock_cons,
      runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write,
      wr_write, Option.bind_some, BitVec.setWidth_eq, h19, h8, h8', l₀, l₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl⟩
  simp only [Proof.Cmac.zero2, Mem.writeW, BitVec.setWidth_eq, Offset.add_add, z0, Nat.reduceDiv]

end Env

end VG.Proof.AesSiv.AArch64
