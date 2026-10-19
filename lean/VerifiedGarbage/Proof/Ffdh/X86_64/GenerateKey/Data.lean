module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Smear
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Data
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH key-generation attempts on x86-64: retained inputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- Only the scalar-range rejection class of the random input is public. -/
structure GkP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  xp : Addr
  yp : Addr
  rp : Addr
  sp : Addr
  sv : Bool

abbrev GkP.w (p : GkP) : Nat := (p.k + 7) / 8
abbrev GkP.params (p : GkP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom
abbrev GkP.pb (p : GkP) : List Byte := p.dom.take p.k
abbrev GkP.P (p : GkP) : Nat := Spec.Rsa.os2ip p.pb
abbrev GkP.mv (p : GkP) : Bool := Spec.Rsa.modulusValid p.P p.k
abbrev GkP.bb (p : GkP) : List Byte := KeyScalar.bnd p.k p.dom
abbrev GkP.ld (p : GkP) : Nat := lead p.bb
abbrev GkP.n (p : GkP) : Nat := p.k - p.ld
abbrev GkP.bc (p : GkP) : Byte := p.bb.getD p.ld 0
abbrev GkP.msk (p : GkP) : BitVec 64 := smear64 p.bc
abbrev GkP.cut (p : GkP) (rb : List Byte) : List Byte := KeyScalar.cut rb p.ld (p.msk.setWidth 8)
abbrev GkP.xb (p : GkP) (rb : List Byte) : List Byte := (p.cut rb).drop p.ld
abbrev GkP.scalar (p : GkP) (rb : List Byte) : Nat := Spec.Ffdh.scalarOfOctets p.params rb

/-- Arguments saved before the scalar output is populated. -/
def GkP.headers (p : GkP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k),
    (sY, p.yp), (sX, p.xp), (sRand, p.rp)]

/-- Arguments for the existing scalar-range and generator-power proofs. -/
def GkP.kp (p : GkP) : CheckPrivate.KpP :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, off p.xp p.ld, p.n, p.yp,
    List.replicate p.k 0, p.sp, p.sv⟩

structure Base (p : GkP) (rb : List Byte) (s : State) : Prop where
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  doml : p.dom.length = p.dl
  rl : rb.length = p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  dom : Src s p.B p.Z p.dp p.dom
  rand : Src s p.B p.Z p.rp rb
  x : OutOk s p.B p.Z p.xp p.k
  y : OutOk s p.B p.Z p.yp p.k
  xy : Apart p.xp p.k p.yp p.k
  xd : Apart p.xp p.k p.dp p.dl
  xr : Apart p.xp p.k p.rp p.k
  yd : Apart p.yp p.k p.dp p.dl
  yr : Apart p.yp p.k p.rp p.k
  hdr : Slots s.mem p.B p.headers
  valid : Spec.Ffdh.privateValid p.params (p.scalar rb) = p.sv

theorem Base.plen {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) : p.pb.length = p.k := by
  simp only [GkP.pb, List.length_take, h.doml]
  rcases h.dl with hd | hd <;> rw [hd] <;> omega

theorem Base.bb_length {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) : p.bb.length = p.k :=
  KeyScalar.bnd_length (by rw [h.doml]; exact h.dl)

theorem Base.ld_lt {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) : p.ld < p.k := by
  have hl := h.bb_length
  have hk := h.k1
  have hn : p.bb ≠ [] := by intro he; rw [he] at hl; simp at hl; omega
  have := lead_lt hn
  rwa [hl] at this

theorem Base.keep {p : GkP} {rb : List Byte} {s t : State} {rs : List Reg} (h : Base p rb s)
    (hf : InScr p.B p.Z s.mem t.mem) (k : Keep rs s t)
    (hh : ∀ e ∈ p.headers, word t.mem p.B (8 * e.1) = word s.mem p.B (8 * e.1)) : Base p rb t :=
  ⟨h.k1, h.k2, h.dl, h.doml, h.rl, h.hZ, h.scr.congr k.2.2,
    h.dom.congrK hf k, h.rand.congrK hf k,
    ⟨fun i hi => by rw [k.2.2]; exact h.x.wr i hi, h.x.sep⟩,
    ⟨fun i hi => by rw [k.2.2]; exact h.y.wr i hi, h.y.sep⟩,
    h.xy, h.xd, h.xr, h.yd, h.yr, fun e he => (hh e he).trans (h.hdr e he), h.valid⟩

/-- The full output buffers retained beside the significant scalar slice. -/
structure Buffers (p : GkP) (rb : List Byte) (s : State) : Prop where
  x : Src s p.B p.Z p.xp (p.cut rb)
  ox : OutOk s p.B p.Z p.xp p.k
  oy : OutOk s p.B p.Z p.yp p.k
  xy : Apart p.xp p.k p.yp p.k
  len : (p.cut rb).length = p.k
  ld : p.ld < p.k

theorem Buffers.keep {p : GkP} {rb : List Byte} {s t : State} {rs : List Reg} (h : Buffers p rb s)
    (hf : InScr p.B p.Z s.mem t.mem) (k : Keep rs s t) : Buffers p rb t :=
  ⟨h.x.congrK hf k, ⟨fun i hi => by rw [k.2.2]; exact h.ox.wr i hi, h.ox.sep⟩,
    ⟨fun i hi => by rw [k.2.2]; exact h.oy.wr i hi, h.oy.sep⟩, h.xy, h.len, h.ld⟩

/-- Only scratch and the two output buffers may change during an attempt. -/
def RunFrame (p : GkP) (m m' : Mem) : Prop :=
  ∀ a, p.Z ≤ ofs p.B a → (∀ i < p.k, a ≠ off p.xp i) →
    (∀ i < p.k, a ≠ off p.yp i) → m' a = m a

theorem RunFrame.refl (p : GkP) (m : Mem) : RunFrame p m m := fun _ _ _ _ => rfl

theorem RunFrame.trans {p : GkP} {m₁ m₂ m₃ : Mem} (h₁ : RunFrame p m₁ m₂)
    (h₂ : RunFrame p m₂ m₃) : RunFrame p m₁ m₃ :=
  fun a ha hx hy => (h₂ a ha hx hy).trans (h₁ a ha hx hy)

theorem RunFrame.of_scr {p : GkP} {m m' : Mem} (h : InScr p.B p.Z m m') : RunFrame p m m' :=
  fun a ha _ _ => h a ha

theorem RunFrame.of_x {p : GkP} {m m' : Mem}
    (h : ∀ a, (∀ i < p.k, a ≠ off p.xp i) → m' a = m a) : RunFrame p m m' :=
  fun a _ hx _ => h a hx

theorem RunFrame.of_y {p : GkP} {m m' : Mem}
    (h : ∀ a, (∀ i < p.k, a ≠ off p.yp i) → m' a = m a) : RunFrame p m m' :=
  fun a _ _ hy => h a hy

theorem RunFrame.of_frm {p : GkP} {m m' : Mem} {rs : List (Nat × Nat)} (h : Frm p.B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) : RunFrame p m m' :=
  .of_scr (InScr.of_frm h hr)

end VG.Proof.Ffdh.X86_64.GenerateKey
