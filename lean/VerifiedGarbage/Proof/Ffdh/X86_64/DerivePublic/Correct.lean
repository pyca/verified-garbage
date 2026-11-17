module

public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Data
public import VerifiedGarbage.Impl.Ffdh.X86_64.DerivePublic
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ffdh.X86_64.DerivePublic.Start`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.DerivePublic.Entry`, which only this module used -/

section

/-! # FFDH public-value derivation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * sDom)) (s.gpr .rdx)).writeW (off B (8 * sDomLen)) (s.gpr .rcx)).writeW (off B (8 * sK)) (s.gpr .r8)).writeW (off B (8 * sY)) (s.gpr .rdi)).writeW (off B (8 * sX)) (s.gpr .r9)).writeW (off B (8 * sXl)) (stackArg s 0))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧
    word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧
    word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .rdx ∧
    word m B (8 * sDomLen) = s.gpr .rcx ∧
    word m B (8 * sK) = s.gpr .r8 ∧
    word m B (8 * sY) = s.gpr .rdi ∧
    word m B (8 * sX) = s.gpr .r9 ∧
    word m B (8 * sXl) = stackArg s 0 ∧ Outside B 0 (8 * 22) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem dvEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .rdx), (sDomLen, s.gpr .rcx), (sK, s.gpr .r8),
        (sY, s.gpr .rdi), (sX, s.gpr .r9), (sXl, stackArg s 0)] ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.rax, .r10, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) (8 * 2)) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.entry save
      simp only [saved, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      dsimp only [VG.Impl.Rsa.X86_64.Crt.stk, stackArgAddr] at ha ⊢
      xrun [State.ea, ws, hdrOff, stackArg, stackArgAddr, hB',
        hw 0 (by decide),
        hw 1 (by decide),
        hw 2 (by decide),
        hw 3 (by decide),
        hw 4 (by decide),
        hw 5 (by decide),
        hw sDom (by decide),
        hw sDomLen (by decide),
        hw sK (by decide),
        hw sY (by decide),
        hw sX (by decide),
        hw sXl (by decide), ha 1 (by decide), ha 0 (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hD, hL, hK, hY, hX, hXl, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hD hL hK hY hX hXl ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hD, hL, hK, hY, hX, hXl]

end VG.Proof.Ffdh.X86_64.DerivePublic

end

end

/-! # FFDH public-value derivation on x86-64: entry, and zeros in y -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/DerivePublic/Context.lean`, which only this module imported.
section

/-! # FFDH public-value derivation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure DvCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  dl : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat ∨ (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat
  yl : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  hZ : 128 * (s.gpr .r8).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdx) (dvDom s)
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  x : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .r9) (dvX s)
  y : OutOk s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdi) (s.gpr .r8).toNat
  yd : Apart (s.gpr .rdi) (s.gpr .r8).toNat (s.gpr .rdx) (s.gpr .rcx).toNat
  yx : Apart (s.gpr .rdi) (s.gpr .r8).toNat (s.gpr .r9) (stackArg s 0).toNat
  ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8

theorem dvCtx_of {s : State} (h : dvPre s) : DvCtx s := by
  obtain ⟨_, hrd, hwr, dyd, dyx, dys, _, dds, dxs, _, wY, wD, wX, wS,
    _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hyl, by omega_using [hsl], Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dds, hxl1, hxl2,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dxs, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega_using [hyl, hi]) (by omega_using [])⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega_using [hyl, hi]) (by omega_using []))
  · simpa only [hyl] using (apart_of dyd (by omega_using []) (by omega_using []))
  · simpa only [hyl] using (apart_of dyx (by omega_using []) (by omega_using []))
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
      congr 2
      omega_using []]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

end VG.Proof.Ffdh.X86_64.DerivePublic
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base)

/-- Private-key validation's parameters: y is the output, read as zeros
once zeroed. -/
def dvOf (s : State) : KpP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .r8).toNat, (s.gpr .rcx).toNat, s.gpr .rdx,
    dvDom s, s.gpr .r9, (stackArg s 0).toNat, s.gpr .rdi, List.replicate (s.gpr .r8).toNat 0, s.gpr .rsp,
    Spec.Ffdh.privateValid (dvA s) (Spec.Rsa.os2ip (dvX s))⟩

/-- y may be written. -/
abbrev YOut (p : KpP) (s : State) : Prop := OutOk s p.B p.Z p.yp p.k

theorem YOut.of_wr {p : KpP} {s t : State} (h : YOut p s) (hw : t.wr = s.wr) : YOut p t :=
  ⟨fun i hi => by rw [hw]; exact h.wr i hi, h.sep⟩

/-- Before y is zeroed: `Base` but for y, which may be written. -/
structure Pre0 (p : KpP) (xb : List Byte) (s : State) : Prop where
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  doml : p.dom.length = p.dl
  yb : p.yb = List.replicate p.k 0
  xlen : xb.length = p.xl
  xl1 : 1 ≤ p.xl
  xl2 : p.xl ≤ p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  dom : Src s p.B p.Z p.dp p.dom
  x : Src s p.B p.Z p.xp xb
  y : YOut p s
  yd : Apart p.yp p.k p.dp p.dl
  yx : Apart p.yp p.k p.xp p.xl
  hdr : Slots s.mem p.B p.headers
  valid : Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip xb) = p.sv

theorem entry_pre0 {s : State} (c : DvCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.entry) s fun t =>
      Pre0 (dvOf s) (dvX s) t ∧ t.gpr .rdi = (dvOf s).B ∧
      InScr (dvOf s).B (dvOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (dvEntry_ok rfl (fun i hi => c.hs.st (by omega_using [hZ, hi])) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (dvOf s).B (dvOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [dvOf]; omega_using [hZ])
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, rfl, bytesAt_length _ _ _, c.xl1, c.xl2, c.hZ,
    c.hs.congr k.2.2, c.dom.congrK hi k, c.x.congrK hi k,
    ⟨fun i hi => by rw [k.2.2]; exact c.y.wr i hi, c.y.sep⟩, c.yd, c.yx, ?_, rfl⟩,
    hd, hi, hs, k.mono (by decide)⟩
  change Slots t.mem (stackArg s 1) (dvOf s).headers
  simp only [KpP.headers, dvOf, ofNat_toNat64]
  intro e he
  exact hh e he

/-- Zeros in y: private-key validation's inputs, with y read as zeros. -/
theorem zero_base {p : KpP} {xb : List Byte} {s : State} (h : Pre0 p xb s) (hd : s.gpr .rdi = p.B) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s fun t =>
      Base p xb t ∧ YOut p t ∧ t.gpr .rdi = p.B ∧
      (∀ a, (∀ i < p.k, a ≠ off p.yp i) → t.mem a = s.mem a) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hk := h.k1
  have hk' := h.k2
  have hZ := h.hZ
  refine WP.mono (zeroOut_ok h.scr hd (by omega_using [hZ]) (by decide) (by decide)
    (h.hdr (sY, p.yp) (by simp [KpP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) (by omega_using [hk]) (by omega_using [hk']) h.y)
    fun t ⟨hz, hf, k⟩ => ?_
  have hout : Outside p.B p.Z (2 ^ 64 - p.Z) s.mem t.mem := by
    intro a ha
    have ha64 : ofs p.B a < 2 ^ 64 := (a - p.B).isLt
    apply hf
    intro i hi he
    have := h.y.sep i hi
    rw [← he] at this
    omega_using [ha, ha64, this]
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d :=
    fun d hd => hout.word (Or.inl hd) (by have := h.scr.nowrap; omega_using [hd, this])
  have hdom : Src t p.B p.Z p.dp p.dom := ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.dom.rd i hi,
    fun i hi => by rw [hf _ (fun j hj => Ne.symm (h.yd j hj i (by rw [← h.doml]; exact hi)))]; exact h.dom.val i hi,
    h.dom.out⟩
  have hx : Src t p.B p.Z p.xp xb := ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.x.rd i hi,
    fun i hi => by rw [hf _ (fun j hj => Ne.symm (h.yx j hj i (by rw [← h.xlen]; exact hi)))]; exact h.x.val i hi,
    h.x.out⟩
  have hy : Src t p.B p.Z p.yp p.yb := by
    rw [h.yb]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < p.k := by simpa only [List.length_replicate] using hi
      obtain ⟨r, hr, hc⟩ := h.y.wr i hi'
      exact ⟨r, List.mem_append_right _ (by rw [k.2.2]; exact hr), hc⟩
    · intro i hi
      rw [hz i (by simpa only [List.length_replicate] using hi)]
      exact (List.getElem_replicate hi).symm
    · intro i hi
      exact h.y.sep i (by simpa only [List.length_replicate] using hi)
  refine ⟨⟨h.k1, h.k2, h.dl, h.doml, by rw [h.yb, List.length_replicate], h.xlen, h.xl1, h.xl2, h.hZ,
    h.scr.congr k.2.2, hdom, hx, hy, ?_, h.valid⟩, h.y.of_wr k.2.2, (k.gpr (by decide)).trans hd,
    hf, fun i hi => hh _ (by omega_using [hZ, hi]), k.mono (by decide)⟩
  intro e he
  rw [hh _ (by
    simp only [KpP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sDom, sDomLen, sK, sY, sX, sXl, sFn] <;> omega_using [hZ])]
  exact h.hdr e he

end VG.Proof.Ffdh.X86_64.DerivePublic

end

end

/-! ### `Ffdh.X86_64.DerivePublic.Main`, which only this module used -/

section

/-! # FFDH public-value derivation on x86-64: the scalar test, the power and y -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base Work StepPost)

/-- 2 for a scalar out of range; else the power's range flag selects 1 or 3. -/
def dvStatus (p : KpP) (xb : List Byte) : Nat := if p.sv then if p.fl xb then 1 else 3 else 2

/-- Only scratch and y change. -/
def DvFrame (p : KpP) (m m' : Mem) : Prop :=
  ∀ a, p.Z ≤ ofs p.B a → (∀ i < p.k, a ≠ off p.yp i) → m' a = m a

theorem DvFrame.trans {p : KpP} {m₁ m₂ m₃ : Mem} (h₁ : DvFrame p m₁ m₂) (h₂ : DvFrame p m₂ m₃) :
    DvFrame p m₁ m₃ := fun a ha hy => (h₂ a ha hy).trans (h₁ a ha hy)

theorem DvFrame.of_scr {p : KpP} {m m' : Mem} (h : InScr p.B p.Z m m') : DvFrame p m m' :=
  fun a ha _ => h a ha

theorem DvFrame.of_y {p : KpP} {m m' : Mem} (h : ∀ a, (∀ i < p.k, a ≠ off p.yp i) → m' a = m a) :
    DvFrame p m m' := fun a _ hy => h a hy

def MainPost (p : KpP) (xb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (dvStatus p xb) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if dvStatus p xb = 1 then p.z xb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ DvFrame p s.mem t.mem ∧
    Keep (.rdi :: mmRegs) s t

theorem status_ok {s : State} {P : Prop} [Decidable P] (ha : s.gpr .rax = bit P) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (if P then 1 else 3) ∧ t.mem = s.mem) ∧ Keep [.rax, .rdx] s t := by
  rw [GenerateKey.bit_eq_bool] at ha
  refine WP.keep _ ?_ rfl
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status
  xrun [ha]
  by_cases h : P <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- Key generation's public output, for private-key validation's power. -/
theorem public_ok {p : KpP} {xb : List Byte} {s : State} (h : CheckPrivate.Value p xb s) (ho : YOut p s) :
    WP isa (seqs GenerateKey.publicOutput) s fun t =>
      Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
      t.gpr .rax = bit (p.fl xb) ∧ t.gpr .rdi = p.B ∧ DvFrame p s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  unfold GenerateKey.publicOutput
  refine wp_seqs_cons (by simp [range])
    (WP.mono (GenerateKey.value_bridge h ho) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := range aY) (by simp [range]) (by simp)
    (WP.mono (Exchange.value_checked hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  refine WP.mono (Exchange.output_ok hv) fun t ⟨hy, hflag, hd, hf, hs₃, k₃⟩ => ?_
  refine ⟨hy, hflag, hd, fun a ha hn => ?_, fun i hi => ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [hf a hn, hi₂ a ha, hi₁ a ha]
  · have a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    have a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    have a₃ : word t.mem p.B (8 * i) = word v.mem p.B (8 * i) := hs₃ i hi
    rw [a₃, a₂, a₁]

/-- The checked generator's power over x, written as y with its status. -/
theorem tail_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : KpP} {xb : List Byte} {mi : BitVec 64}
    {s : State} (h : Work p xb mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (ho : YOut p s) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail M.mm E.code (.seq (.block r2Head) R.code))) s
      fun t => t.gpr .rax = BitVec.ofNat 64 (if p.fl xb then 1 else 3) ∧ t.gpr .rdi = p.B ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
        (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ DvFrame p s.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail
  simp only [List.append_assoc]
  refine wp_seqs_append (a := [.seq (.block r2Head) R.code]) (by simp) (by simp)
    (WP.mono (CheckPrivate.work_ready M R h hd hm) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sG sK sX sXl)
    (b := GenerateKey.publicOutput ++ [.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status])
    (by simp [pow]) (by simp)
    (WP.mono (CheckPrivate.ready_value M E hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  refine wp_seqs_append (a := GenerateKey.publicOutput) (by simp [GenerateKey.publicOutput]) (by simp)
    (WP.mono (public_ok hv ((ho.of_wr k₁.2.2).of_wr k₂.2.2)) fun z ⟨hy, hax, hdz, hf, hs₃, k₃⟩ => ?_)
  simp only [seqs]
  refine WP.mono (status_ok hax) fun t ⟨⟨ha, hmt⟩, k₄⟩ => ?_
  refine ⟨ha, (k₄.gpr (by decide)).trans hdz, by rw [hmt]; exact hy, fun i hi => ?_, ?_,
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · have a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    have a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    rw [hmt, hs₃ i hi, a₂, a₁]
  · intro a ha hn
    rw [hmt, hf a ha hn, hi₂ a ha, hi₁ a ha]

theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs (((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl) ++
          (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++
            ([.block [.alu .test .rax (.reg .rax)], .ite .e (retInner 2)
              (seqs (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail M.mm E.code (.seq (.block r2Head) R.code)))] :
              List (Prog isa)))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : KpP} {xb : List Byte} {s : State}
    (h : Base p xb s) (hy : YOut p s) (hyb : p.yb = List.replicate p.k 0) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (MainPost p xb s) := by
  rw [main_eq]
  have hodd := (valid_facts hm h.k1).1
  refine wp_seqs_append (by simp [pSetup, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (WP.mono (CheckPrivate.setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (CheckPrivate.scalar_ok hw₁ hd₁ hodd) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  simp only [seqs]
  refine WP.seq (WP.mono (test_bit_ok S₂.1.2.2) fun u₃ ⟨hz, hmem, k⟩ => ?_)
  have hw₃ := hw₂.keep hmem k
  have hd₃ := (k.gpr (by decide)).trans hd₂
  have S₃ : StepPost p u₂ (fun _ => True) u₃ := ⟨trivial, by rw [hmem]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hmem]), k.mono (by decide)⟩
  have H := (S₁.trans S₂).trans S₃
  have hy₃ : YOut p u₃ := hy.of_wr H.2.2.2.2.2
  refine WP.ite (!decide (p.sv = true)) (by simp [eval, hz]) (fun hs => ?_) (fun hs => ?_)
  · have hsv : p.sv = false := by cases h : p.sv <;> simp_all
    unfold retInner
    refine WP.seq (WP.mono (leave_ok (hw₃.mem.ctx hd₃)) fun u₄ ⟨hd₄, hm₄, k₄⟩ => ?_)
    refine WP.mono (ret_ok u₄ (r := 2) (by decide)) fun t ⟨ha, hm₅, k₅⟩ => ?_
    have hst : dvStatus p xb = 2 := by simp only [dvStatus, hsv, Bool.false_eq_true, ↓reduceIte]
    have hyt : Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
      have hb := GenerateKey.bytes_src hw₃.base.y
      rw [hm₅, hm₄]
      rwa [hyb, List.length_replicate] at hb
    refine ⟨by rw [ha, hst], (k₅.gpr (by decide)).trans hd₄, ?_, fun i hi => ?_,
      fun a ha _ => ?_, keep_trans H.2.2.2 ((k₄.trans k₅).mono (by decide))⟩
    · rw [hyt, hst, ite_eq_right (by decide), i2osp_zero']
    · rw [hm₅, hm₄]; exact H.2.2.1 i hi
    · rw [hm₅, hm₄]; exact H.2.1 a ha
  · have hsv : p.sv = true := by cases h : p.sv <;> simp_all
    refine WP.mono (tail_ok M E R hw₃ hd₃ hm hy₃) fun t ⟨ha, hd', hyt, hs', hf', k'⟩ => ?_
    have hst : dvStatus p xb = if p.fl xb then 1 else 3 := by simp only [dvStatus, hsv, ↓reduceIte]
    refine ⟨by rw [hst]; exact ha, hd', ?_, fun i hi => (hs' i hi).trans (H.2.2.1 i hi),
      (DvFrame.of_scr H.2.1).trans hf', keep_trans H.2.2.2 k'⟩
    rw [hyt, hst]
    by_cases hf : p.fl xb
    · rw [ite_eq_left hf, ite_eq_left hf, ite_eq_left rfl]
    · rw [ite_eq_right hf, ite_eq_right hf, ite_eq_right (by decide)]

end VG.Proof.Ffdh.X86_64.DerivePublic

end

end


/-! # FFDH public-value derivation on x86-64: correctness and ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base)
open VG.Spec.Ffdh

theorem dvStatus_eq {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hm : p.mv = true) (ha : parametersValid p.params = true) :
    dvStatus p xb = keyStatus p.params (Spec.Rsa.os2ip xb) := by
  cases hsv : p.sv with
  | false =>
    have hx : privateValid p.params (Spec.Rsa.os2ip xb) = false := h.valid.trans hsv
    have hr := (VG.Proof.Ffdh.keyStatus_scalar p.params (Spec.Rsa.os2ip xb)).mpr hx
    simpa only [dvStatus, hsv, Bool.false_eq_true, ↓reduceIte] using hr.symm
  | true =>
    have hx : privateValid p.params (Spec.Rsa.os2ip xb) = true := h.valid.trans hsv
    rw [VG.Proof.Ffdh.keyStatus_power ha _ hx]
    simp only [dvStatus, hsv, ↓reduceIte]
    congr 1
    apply propext
    change (1 < p.z xb ∧ 2 * (p.z xb / 2) + 1 < p.P) ↔ _
    rw [lt_pm1 (valid_facts hm h.k1).1]
    rfl

theorem dvStatus_lt (p : KpP) (xb : List Byte) : dvStatus p xb < 2 ^ 32 := by
  unfold dvStatus
  split
  · split <;> decide
  · decide

theorem main_spec {p : KpP} {xb : List Byte} {s u t : State} (hb : Base p xb u)
    (hm : p.mv = true) (ha : parametersValid p.params = true) (h : MainPost p xb s t) :
    ((t.gpr .rax).setWidth 32).toNat = keyStatus p.params (Spec.Rsa.os2ip xb) ∧
      if keyStatus p.params (Spec.Rsa.os2ip xb) = 1 then
        Spec.Rsa.bytesAt t.mem p.yp p.k =
          Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (Spec.Rsa.os2ip xb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hy, _⟩ := h
  have hst := dvStatus_eq hb hm ha
  have hlt := dvStatus_lt p xb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : dvStatus p xb = 1
    · simp only [ite_eq_left hs] at hy ⊢
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hy ⊢
      rw [hy, i2osp_zero']

theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : dvPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => dvPost s t ∧ t.gpr .rdi = (dvOf s).B ∧ DvFrame (dvOf s) s.mem t.mem ∧
        (∀ i < 6, word t.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := dvCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body
  refine WP.seq (WP.mono (entry_pre0 c) fun u ⟨h0, hd, hi, hs, k⟩ => ?_)
  refine WP.seq (WP.mono (zero_base h0 hd) fun u' ⟨hb, hy, hd', hf', hs', k'⟩ => ?_)
  refine WP.seq (WP.mono (CheckPrivate.dom_base hb hd') fun v ⟨hb', hz, hd'', hG, hQ, hi'', hs'', k''⟩ => ?_)
  have H : DvFrame (dvOf s) s.mem v.mem :=
    ((DvFrame.of_scr hi).trans (DvFrame.of_y hf')).trans (DvFrame.of_scr hi'')
  have K := keep_trans (keep_trans k k') k''
  have hS : ∀ i < 6, word v.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs'' i hi).trans ((hs' i hi).trans (hs i hi))
  have hyv : YOut (dvOf s) v := hy.of_wr k''.2.2
  refine WP.ite (!(dvOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (dvOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd'', fun a ha hn => by rw [hmem]; exact H a ha hn,
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv
    have hm' := domainValid_mod hv
    change (dvOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (dvOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    refine WP.mono (main_ok M E R hb' hyv rfl hd'' hG hQ hm) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, H.trans hframe, (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    intro hv
    have hp : parametersValid (dvOf s).params = true := by
      unfold domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    have spec := main_spec hb' hm hp hmain
    exact spec

theorem dv_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : ctlOk (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) = true) (s : State) (h : dvContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ dvContract.post s t := by
  have hpre := h
  have c := dvCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ dvContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_ctl hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code
  refine WP.seq (WP.mono (body_ok M E R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega_arith) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_
    intro j hj he
    exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega_arith))
  · change dvPost s t
    unfold dvPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.DerivePublic
