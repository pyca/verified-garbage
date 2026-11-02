module

-- separate module: its proofs (about 4 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Call
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Deterministic ECDSA on RISC-V: the contract, the layout and the calls

The contract the proof is written against (`rfcR`), which each instance's
shared contract implies; what the proof needs of an instance (`Rfc`): the
hash function's streaming functions with HMAC's over them, constant time,
the code's configuration, the shared contract's instance, and the curve's
(`Kit`: its scalars' words, the functions of its order, and the signature
with a given `k` with its constant tables, if any). The proofs
start from the state the frame's body starts in (`s₀`, with the stack
pointer at the frame and `X` bytes of stack below it for the functions we
call), whose precondition is `Pre`; `KR` is what holds from the end of the
prologue on: the regions, the stack pointer, the registers holding the
pointers, our caller's registers in the save area, and memory outside the
frame, `out`, `scratch` and the stack below the frame (`wrs`).

The calls of HMAC's `init` and `finalize` (against the contracts of their
generic proofs, `WP.callAny`, since they allocate their working space on the
stack), of the streaming `update` (`HashOK.callUpd_ok`) and of the signature
with a given `k` (the kit's `core_call`): what each needs of the state it is
called from, and what holds when it returns; and, for HMAC's and the
signature's, that two runs of the call with the same arguments leak the
same trace (`RelCT.call`, the kit's `core_rel`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The contract -/

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- `sign(out, d, digest, scratch)`, with `N` bytes of stack. -/
def rfcR (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .a1, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .a2, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    let stk : Region := below s.sp N
    s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ s.sp.toNat % 16 = 0 ∧ N ≤ s.sp.toNat ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .a0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    match (result I s.mem (s.gpr .a1) (s.gpr .a2)).1 with
    | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * I.ecdsa.curve.len) = Spec.Ecdsa.encode I.ecdsa.curve rs
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * I.ecdsa.curve.len) =
          List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
    (result I s₁.mem (s₁.gpr .a1) (s₁.gpr .a2)).2 = (result I s₂.mem (s₂.gpr .a1) (s₂.gpr .a2)).2

/-- `rfcR` with the tables `K` the signature with a given `k` reads
(`abi.withConsts`): `rfcR` for the state without them, and what they add. -/
def rfcRC (K : List (String × List (BitVec 64))) (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract isa where
  pre s := (rfcR I N).pre (stripConsts K s) ∧ ConstsOk K N s
  post := (rfcR I N).post
  pub s₁ s₂ := (rfcR I N).pub s₁ s₂ ∧ ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-- A state satisfying the precondition, for scalars of `Q` bytes and a
digest of `D` bytes. -/
def satState (Q D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, Q⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]

/-! ## The instance -/

/-- HMAC's `init`, with its frame and its callees' stack. -/
abbrev hiK (H : Hash) (SH : Spec.Hmac.StreamingHash) : Contract isa := initG SH (H.ibytes + H.F)

/-- HMAC's `finalize`, with its frame and its callees' stack. -/
abbrev hfK (H : Hash) (SH : Spec.Hmac.StreamingHash) : Contract isa := finG SH (H.fbytes + H.F)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

/-- What a call of the signature with a given `k`, of `Q` bytes scalars,
needs: `out` at `o`, `d`, the digest and `k` at `d`, `g` and `k`, the working
space at `w`, and the tables `K` apart from what it writes. -/
structure CoreArgs (Q : Nat) (K : List (String × List (BitVec 64))) (s : State) (o d g k w : Addr) : Prop where
  a0 : s.gpr .a0 = o
  a1 : s.gpr .a1 = d
  a2 : s.gpr .a2 = g
  a3 : s.gpr .a3 = k
  a4 : s.gpr .a4 = w
  d_ow : Region.Disjoint ⟨o, 2 * Q⟩ ⟨w, 8192⟩
  d_dw : Region.Disjoint ⟨d, Q⟩ ⟨w, 8192⟩
  d_gw : Region.Disjoint ⟨g, Q⟩ ⟨w, 8192⟩
  d_kw : Region.Disjoint ⟨k, Q⟩ ⟨w, 8192⟩
  no : o.toNat + 2 * Q ≤ 2 ^ 64
  nd : d.toNat + Q ≤ 2 ^ 64
  ng : g.toNat + Q ≤ 2 ^ 64
  nk : k.toNat + Q ≤ 2 ^ 64
  nw : w.toNat + 8192 ≤ 2 ^ 64
  wa : w.toNat % 8 = 0
  held : Abi.constsHeld s.mem (fun name => s.syms name) K
  tfit : ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ 64
  tal : ∀ t ∈ constRegs K s, t.base.toNat % 64 = 0
  t_o : ∀ t ∈ constRegs K s, t.Disjoint ⟨o, 2 * Q⟩
  t_w : ∀ t ∈ constRegs K s, t.Disjoint ⟨w, 8192⟩
  hc : RISCV64.Covers ([⟨d, Q⟩, ⟨g, Q⟩, ⟨k, Q⟩] ++ constRegs K s ++ [⟨o, 2 * Q⟩, ⟨w, 8192⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨o, 2 * Q⟩, ⟨w, 8192⟩] s.wr

/-- The signature of the digest at `g` with the key at `d` and the secret
number at `k`, of `Q` bytes each, as the specification computes it. -/
abbrev sgOf (E : Spec.Ecdsa.Instance) (Q : Nat) (m : Mem) (d g k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith E.curve (Spec.Weierstrass.ofBytes (bytesAt m d Q))
    (Spec.Ecdsa.hashToInt E.curve (bytesAt m g Q)) (Spec.Weierstrass.ofBytes (bytesAt m k Q))

/-- What the proof needs of the curve: its scalars' 64-bit words, its ECDSA
instance, the functions of its order `n` (whose addition `bits2octets`
calls), and the signature with a given `k`, the tables it reads, its
correctness and its constant time by call. -/
structure Kit where
  nw : Nat
  E : Spec.Ecdsa.Instance
  FN : VG.Impl.Weierstrass.RISCV64.Field
  FNok : VG.Proof.Weierstrass.RISCV64.FieldOk FN
  FNk : FN.S.k = nw
  FNm : FN.S.m = E.curve.n
  len : E.curve.len = 8 * nw
  nbits : Spec.Ecdsa.nBits E.curve = 64 * nw
  two : 2 ^ (64 * nw) < 2 * E.curve.n
  nw4 : nw = 4 ∨ nw = 6
  coreC : Prog isa
  K : List (String × List (BitVec 64))
  core_call : ∀ {nm : String} {s : State} {o d g k w : Addr}, CoreArgs (8 * nw) K s o d g k w →
    ∀ {Q : State → Prop}, (∀ s', After s [⟨o, 2 * (8 * nw)⟩, ⟨w, 8192⟩] s' →
      (match sgOf E (8 * nw) s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem o (2 * (8 * nw)) = Spec.Ecdsa.encode E.curve rs
        | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem o (2 * (8 * nw)) = List.replicate (2 * (8 * nw)) 0) → Q s') →
    WP isa (.call nm coreC) s Q
  core_rel : ∀ {nm : String} {Q : State → State → Prop} {o d g k w : Addr} {f : String → BitVec 64},
    (∀ s s', Q s s' → CoreArgs (8 * nw) K s o d g k w ∧ CoreArgs (8 * nw) K s' o d g k w ∧ s.sp = s'.sp ∧
      ∀ c ∈ K, s.syms c.1 = f c.1 ∧ s'.syms c.1 = f c.1) →
    RelCT isa Q (.call nm coreC) fun _ _ => True

/-- What the proof needs of an instance: a curve's kit with a hash function. -/
structure Rfc where
  c : Cfg
  hH : HashOK c.H
  hiCt : ConstantTime isa (hiK c.H hH.SH).pre (hiK c.H hH.SH).pub c.H.init
  hfCt : ConstantTime isa (hfK c.H hH.SH).pre (hfK c.H hH.SH).pub c.H.finalize
  I : Spec.Ecdsa.Rfc6979.Instance
  kit : Kit
  hE : I.ecdsa = kit.E
  hHash : I.hash = hH.SH.H
  hD : I.hashLen = c.H.D
  hnw : c.nw = kit.nw
  hDQ : 8 * kit.nw ≤ c.H.D
  hD48 : c.H.D ≤ 48
  hS : c.H.S ≤ 192
  hct : c.tries = I.tries
  hT : 1 ≤ c.tries
  hT' : c.tries < 2048
  hFN : c.FN = kit.FN
  hcC : c.coreC = kit.coreC

namespace Rfc

variable (P : Rfc)

/-- The bytes of stack the functions we call use below the frame. -/
def X : Nat := max P.c.H.ibytes P.c.H.fbytes + P.c.H.F

/-- The stack the function uses. -/
def N : Nat := P.c.frB + P.X

end Rfc

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev out : Addr := s₀.gpr .a0
abbrev dk : Addr := s₀.gpr .a1
abbrev dg : Addr := s₀.gpr .a2
abbrev scr : Addr := s₀.gpr .a3
/-- An address in the frame, and a part of it. -/
abbrev sA (o : Nat) : Addr := s₀.sp + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨sA s₀ o, n⟩
/-- An address in `scratch`, and a part of it. -/
abbrev cA (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev cR (o n : Nat) : Region := ⟨cA s₀ o, n⟩
abbrev scrR : Region := ⟨scr s₀, 8192⟩
/-- The save area. -/
abbrev svR : Region := sR s₀ 0 64

end

/-- The scalars' bytes. -/
abbrev Rfc.Q (P : Rfc) : Nat := 8 * P.kit.nw

/-- `out`, `d`, and the frame. -/
abbrev outR (P : Rfc) (s₀ : State) : Region := ⟨out s₀, 2 * P.Q⟩
abbrev dR (P : Rfc) (s₀ : State) : Region := ⟨dk s₀, P.Q⟩
abbrev frR (P : Rfc) (s₀ : State) : Region := ⟨s₀.sp, P.c.frB⟩

/-- The digest. -/
abbrev dgR (P : Rfc) (s₀ : State) : Region := ⟨dg s₀, P.c.H.D⟩
/-- The stack below the frame the functions we call use. -/
abbrev stk (P : Rfc) (s₀ : State) : Region := below s₀.sp P.X
/-- Everything the code writes. -/
abbrev wrs (P : Rfc) (s₀ : State) : List Region := [frR P s₀, outR P s₀, scrR s₀, stk P s₀]

/-- The state the frame's body starts in. -/
structure Pre (P : Rfc) (s₀ : State) : Prop where
  rd : s₀.rd = [dR P s₀, dgR P s₀] ++ constRegs P.kit.K s₀
  wr : s₀.wr = [frR P s₀, outR P s₀, scrR s₀]
  o_d : (outR P s₀).Disjoint (dR P s₀)
  o_g : (outR P s₀).Disjoint (dgR P s₀)
  o_c : (outR P s₀).Disjoint (scrR s₀)
  d_c : (dR P s₀).Disjoint (scrR s₀)
  g_c : (dgR P s₀).Disjoint (scrR s₀)
  f_o : (frR P s₀).Disjoint (outR P s₀)
  f_d : (frR P s₀).Disjoint (dR P s₀)
  f_g : (frR P s₀).Disjoint (dgR P s₀)
  f_c : (frR P s₀).Disjoint (scrR s₀)
  b_o : (stk P s₀).Disjoint (outR P s₀)
  b_d : (stk P s₀).Disjoint (dR P s₀)
  b_g : (stk P s₀).Disjoint (dgR P s₀)
  b_c : (stk P s₀).Disjoint (scrR s₀)
  al : s₀.sp.toNat % 16 = 0
  spX : P.X ≤ s₀.sp.toNat
  top : s₀.sp.toNat + P.c.frB ≤ 2 ^ 64
  no : (out s₀).toNat + 2 * P.Q ≤ 2 ^ 64
  nd : (dk s₀).toNat + P.Q ≤ 2 ^ 64
  ng : (dg s₀).toNat + P.c.H.D ≤ 2 ^ 64
  nc : (scr s₀).toNat + 8192 ≤ 2 ^ 64
  ca : (scr s₀).toNat % 8 = 0
  /-- The tables: their words, where, apart from what the code writes. -/
  held : Abi.constsHeld s₀.mem (fun name => s₀.syms name) P.kit.K
  tal : ∀ t ∈ constRegs P.kit.K s₀, t.base.toNat % 64 = 0
  tfit : ∀ t ∈ constRegs P.kit.K s₀, t.base.toNat + t.len ≤ 2 ^ 64
  t_w : ∀ t ∈ constRegs P.kit.K s₀, ∀ r ∈ wrs P s₀, t.Disjoint r

/-! ## The sizes -/

/-- The sizes the proofs use. -/
structure Sz (P : Rfc) : Prop where
  N : 0 < P.c.H.N ∧ P.c.H.N ≤ 64
  B : P.c.H.B = 64 ∨ P.c.H.B = 128
  S : P.c.H.S = P.c.H.N + P.c.H.B
  S192 : P.c.H.S ≤ 192
  D : P.Q ≤ P.c.H.D ∧ P.c.H.D ≤ 48
  Q : (P.Q = 32 ∨ P.Q = 48) ∧ P.Q ≤ 48 ∧ P.c.Q = P.Q ∧ P.c.frB = 192 + P.Q
  HF : P.c.H.F ≤ 1024
  X : P.c.H.ibytes + P.c.H.F ≤ P.X ∧ P.c.H.fbytes + P.c.H.F ≤ P.X ∧ P.c.H.F ≤ P.X ∧ P.X ≤ 4096

theorem sizes (P : Rfc) : Sz P := by
  have hl := P.hH.lay
  have hB := P.hH.hB64
  have := P.kit.nw4
  refine ⟨P.hH.hN, hB, rfl, P.hS, ⟨P.hDQ, P.hD48⟩, ⟨by simp only [Rfc.Q]; omega, by simp only [Rfc.Q]; omega, by
    simp only [Cfg.Q, Rfc.Q, P.hnw], by simp only [Cfg.frB, Cfg.Q, fH, P.hnw]⟩, P.hH.hF, ?_⟩
  have := hl.ibytes; have := hl.fbytes; have := P.hH.hF
  simp only [Rfc.X]
  omega

section
variable {P : Rfc} {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem part_sub {o n : Nat} (h : o + n ≤ P.c.frB) : Region.Sub (sR s₀ o n) (frR P s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 4096) (hb : b + n ≤ 4096) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) :=
  Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem scr_sub {o n : Nat} (h : o + n ≤ 8192) : Region.Sub (cR s₀ o n) (scrR s₀) :=
  Offset.sub_base _ h

theorem scr_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8192) (hb : b + n ≤ 8192) :
    Region.Disjoint (cR s₀ a m) (cR s₀ b n) :=
  Offset.disjoint _ h (by have := hp.nc; omega) (by have := hp.nc; omega)

theorem fr_wr {s : State} (hwr : s.wr = s₀.wr) : frR P s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp
theorem out_wr {s : State} (hwr : s.wr = s₀.wr) : outR P s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp
theorem scr_wr {s : State} (hwr : s.wr = s₀.wr) : scrR s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem in_fr {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ P.c.frB) :
    InRegions s.wr (sA s₀ o) n :=
  ⟨_, fr_wr hp hwr, Offset.contains_base _ h (by have := (sizes P).Q; omega)⟩

theorem in_fr' {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ P.c.frB) :
    InRegions (s.rd ++ s.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (fr_wr hp hwr), Offset.contains_base _ h (by have := (sizes P).Q; omega)⟩

/-- The frame is apart from the stack below it. -/
theorem f_s : (frR P s₀).Disjoint (stk P s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spX; have := s₀.sp.isLt; omega)

/-- The stack below the stack pointer, within `stk`. -/
theorem below_stk {n : Nat} (hn : n ≤ P.X) : Region.Sub (below s₀.sp n) (stk P s₀) :=
  below_sub hn (by have := hp.spX; have := s₀.sp.isLt; omega)

end

/-! ## What every piece keeps -/

/-- The callee-saved registers the code never writes. -/
abbrev nvRegs : List Reg := [.s6, .s7, .s8, .s9, .s10, .s11]

/-- The registers and memory kept from the end of the prologue on. -/
structure KR (P : Rfc) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s0 : s.gpr .s0 = scr s₀
  s1 : s.gpr .s1 = s₀.sp
  s2 : s.gpr .s2 = out s₀
  s3 : s.gpr .s3 = dk s₀
  s4 : s.gpr .s4 = dg s₀
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r
  saved : Spill.Saved s₀.sp s₀.gpr saved s.mem
  frame : Frame (wrs P s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s6, .s7, .s8, .s9, .s10, .s11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved := by decide

theorem saved_fits : Spill.Fits saved := by
  refine ⟨fun q hq => ?_, by decide⟩
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem saved_in : ∀ q ∈ saved, 0 ≤ q.2 ∧ q.2 + 8 ≤ 0 + 64 := by
  intro q hq
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {P : Rfc} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR P s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, Region.Disjoint (svR s₀) r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs P s₀, Region.Sub r r') : KR P s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.s0, (hg _ (by simp)).trans h.s1,
    (hg _ (by simp)).trans h.s2, (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s4,
    fun r hr => (hg r (by revert r; decide)).trans (h.nv r hr),
    h.saved.frame_in saved_in hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s s' : State} (h : KR P s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR P s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

open VG.RISCV64.Steps (Upd) in
theorem KR.upd {s s' : State} (h : KR P s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s s' d v) : KR P s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A part of the frame after the save area, `out`, `scratch`, or the stack
below the frame. -/
def Wk (P : Rfc) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ 64 ≤ o ∧ o + n ≤ P.c.frB) ∨ Region.Sub r (outR P s₀) ∨ Region.Sub r (scrR s₀) ∨
    ∃ n, r = below s₀.sp n ∧ n ≤ P.X

theorem Wk.ok (hp : Pre P s₀) {r : Region} (h : Wk P s₀ r) :
    Region.Disjoint (svR s₀) r ∧ ∃ r' ∈ wrs P s₀, Region.Sub r r' := by
  have sv : Region.Sub (svR s₀) (frR P s₀) := part_sub (by have := (sizes P).Q; omega)
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | h | ⟨n, rfl, hn⟩
  · exact ⟨part_disj (s₀ := s₀) (.inl h₁) (by have := (sizes P).Q; omega) (by have := (sizes P).Q; omega),
      _, by simp, part_sub (s₀ := s₀) h₂⟩
  · exact ⟨(hp.f_o.sub_left sv).sub_right h, _, by simp, h⟩
  · exact ⟨(hp.f_c.sub_left sv).sub_right h, _, by simp, h⟩
  · exact ⟨((f_s hp).sub_left sv).sub_right (below_stk hp hn), _, by simp, below_stk hp hn⟩

/-- What a call leaves, writing parts of the frame after the save area,
`out`, `scratch` and the stack below the frame. -/
theorem KR.call (hp : Pre P s₀) {s s' : State} (h : KR P s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hw : ∀ r ∈ rs, Wk P s₀ r) : KR P s₀ s' :=
  h.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr)) hf (fun r hr => (Wk.ok hp (hw r hr)).1)
    (fun r hr => (Wk.ok hp (hw r hr)).2)

/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR P s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs P s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem KR.dBytes (hp : Pre P s₀) {s : State} (hk : KR P s₀ s) :
    bytesAt s.mem (dk s₀) P.Q = bytesAt s₀.mem (dk s₀) P.Q :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.f_d.symm
    · exact hp.o_d.symm
    · exact hp.d_c
    · exact hp.b_d.symm) (by have := (sizes P).Q; omega)

theorem KR.dgBytes (hp : Pre P s₀) {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.c.H.D) :
    bytesAt s.mem (dg s₀) n = bytesAt s₀.mem (dg s₀) n :=
  hk.bytes (fun r hr => by
    have sub : Region.Sub ⟨dg s₀, n⟩ (dgR P s₀) := Region.sub_prefix hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.f_g.sub_right sub).symm
    · exact (hp.o_g.sub_right sub).symm
    · exact hp.g_c.sub_left sub
    · exact (hp.b_g.sub_right sub).symm) (by have := (sizes P).D; omega)

end

/-! ## The calls -/

section
variable (P : Rfc)

theorem hi_sdepth : sdepth P.c.H.init ≤ P.c.H.ibytes + P.c.H.F := by
  have := P.hH.initSd; have := P.hH.updSd; have := P.hH.finSd
  simp only [Hash.init, Hash.initMain, Hash.longKey, Hash.padKey, Hash.updBlock, Hash.callInit, Hash.callUpd,
    Hash.callFin, Hash.keyLoop, Hash.padLoop, sdepth, Instr.frameBytes]
  omega

theorem hf_sdepth : sdepth P.c.H.finalize ≤ P.c.H.fbytes + P.c.H.F := by
  have := P.hH.updSd; have := P.hH.finSd
  simp only [Hash.finalize, Hash.finalizeMain, Hash.callUpd, Hash.callFin, sdepth, Instr.frameBytes]
  omega

theorem hi_ok : ∀ s, (hiK P.c.H P.hH.SH).pre s → ∃ t s', Exec isa P.c.H.init s t s' ∧
    abiPreserved s s' ∧ (hiK P.c.H P.hH.SH).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Init.correct P.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

theorem hf_ok : ∀ s, (hfK P.c.H P.hH.SH).pre s → ∃ t s', Exec isa P.c.H.finalize s t s' ∧
    abiPreserved s s' ∧ (hfK P.c.H P.hH.SH).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Finalize.correct P.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

end

/-- What a call of HMAC's `init` needs of the state it is called from: the
key's `kl` bytes at `k` and the states at `inn` and `ou`. -/
structure HiArgs (P : Rfc) (s : State) (inn ou k : Addr) (kl : Nat) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a2 : s.gpr .a2 = k
  a3 : (s.gpr .a3).toNat = kl
  al : s.sp.toNat % 16 = 0
  sp : P.c.H.ibytes + P.c.H.F ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, P.c.H.S⟩ ⟨ou, P.c.H.S⟩
  d_ki : Region.Disjoint ⟨k, kl⟩ ⟨inn, P.c.H.S⟩
  d_ko : Region.Disjoint ⟨k, kl⟩ ⟨ou, P.c.H.S⟩
  b_i : (below s.sp (P.c.H.ibytes + P.c.H.F)).Disjoint ⟨inn, P.c.H.S⟩
  b_o : (below s.sp (P.c.H.ibytes + P.c.H.F)).Disjoint ⟨ou, P.c.H.S⟩
  b_k : (below s.sp (P.c.H.ibytes + P.c.H.F)).Disjoint ⟨k, kl⟩
  hc : RISCV64.Covers ([⟨k, kl⟩] ++ [⟨inn, P.c.H.S⟩, ⟨ou, P.c.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, P.c.H.S⟩, ⟨ou, P.c.H.S⟩] s.wr

section
variable {P : Rfc}

theorem HiArgs.pre {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs P s inn ou k kl) :
    (hiK P.c.H P.hH.SH).pre (s.callEntry.withRegions [⟨k, kl⟩]
      [⟨inn, P.hH.SH.stateBytes⟩, ⟨ou, P.hH.SH.stateBytes⟩]) := by
  have hS := P.hH.hS
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, hS]
  exact ⟨trivial, trivial, h.d_io, h.d_ki, h.d_ko, h.al, h.sp, h.b_i, h.b_o, h.b_k⟩

/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs P s inn ou k kl) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, P.c.H.S⟩, ⟨ou, P.c.H.S⟩] ++ [below s.sp (P.c.H.ibytes + P.c.H.F)]) s' →
      P.hH.SH.Repr s'.mem inn (xorPad (blockKey P.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      P.hH.SH.Repr s'.mem ou (xorPad (blockKey P.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call P.c.hiN P.c.H.init) s Q := by
  have hS := P.hH.hS
  have hl := P.hH.lay
  have c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = k := (State.callEntry_gpr _ (by decide)).trans h.a2
  have c3 : (s.callEntry.gpr .a3).toNat = kl := by rw [State.callEntry_gpr _ (by decide), h.a3]
  refine WP.callAny (k := hiK P.c.H P.hH.SH) (hi_ok P) (rd := [⟨k, kl⟩])
    (wr := [⟨inn, P.hH.SH.stateBytes⟩, ⟨ou, P.hH.SH.stateBytes⟩]) h.pre (by rw [hS]; exact h.hc)
    (by rw [hS]; exact h.hw) ?_ (by have := hi_sdepth P; have := hl.ibytes; have := hl.F; omega)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
    c3] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
  rw [hS] at hf
  exact Frame.below_mono hf (hi_sdepth P) (by have := hl.ibytes; have := hl.F; omega)

/-- Two runs of a call of HMAC's `init` with the same arguments. -/
theorem hi_rel {Q : State → State → Prop} {inn ou k : Addr} {kl : Nat}
    (h : ∀ s s', Q s s' → HiArgs P s inn ou k kl ∧ HiArgs P s' inn ou k kl ∧ s.sp = s'.sp) :
    RelCT isa Q (.call P.c.hiN P.c.H.init) fun _ _ => True := by
  have hS := P.hH.hS
  refine RelCT.call (hi_ok P) P.hiCt [⟨k, kl⟩] [⟨inn, P.hH.SH.stateBytes⟩, ⟨ou, P.hH.SH.stateBytes⟩]
    fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2]
  simp only [true_and]
  exact ⟨BitVec.eq_of_toNat_eq (a.a3.trans a'.a3.symm), e⟩

end

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou` and `out` at `o`. -/
structure HfArgs (P : Rfc) (s : State) (inn ou o : Addr) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a3 : s.gpr .a3 = o
  al : s.sp.toNat % 16 = 0
  sp : P.c.H.fbytes + P.c.H.F ≤ s.sp.toNat
  d_iu : Region.Disjoint ⟨inn, P.c.H.S⟩ ⟨ou, P.c.H.S⟩
  d_io : Region.Disjoint ⟨inn, P.c.H.S⟩ ⟨o, P.c.H.D⟩
  d_uo : Region.Disjoint ⟨ou, P.c.H.S⟩ ⟨o, P.c.H.D⟩
  b_i : (below s.sp (P.c.H.fbytes + P.c.H.F)).Disjoint ⟨inn, P.c.H.S⟩
  b_u : (below s.sp (P.c.H.fbytes + P.c.H.F)).Disjoint ⟨ou, P.c.H.S⟩
  b_o : (below s.sp (P.c.H.fbytes + P.c.H.F)).Disjoint ⟨o, P.c.H.D⟩
  hc : RISCV64.Covers ([⟨ou, P.c.H.S⟩] ++ [⟨inn, P.c.H.S⟩, ⟨o, P.c.H.D⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, P.c.H.S⟩, ⟨o, P.c.H.D⟩] s.wr

section
variable {P : Rfc}

theorem HfArgs.pre {s : State} {inn ou o : Addr} (h : HfArgs P s inn ou o) :
    (hfK P.c.H P.hH.SH).pre (s.callEntry.withRegions [⟨ou, P.hH.SH.stateBytes⟩]
      [⟨inn, P.hH.SH.stateBytes⟩, ⟨o, P.hH.SH.digestBytes⟩]) := by
  have hS := P.hH.hS; have hD := P.hH.hD
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a3, hS, hD]
  exact ⟨trivial, trivial, h.d_iu, h.d_io, h.d_uo, h.al, h.sp, h.b_i, h.b_u, h.b_o⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `a2`, into `o`. -/
theorem hf_call {s : State} {inn ou o : Addr} (h : HfArgs P s inn ou o) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, P.c.H.S⟩, ⟨o, P.c.H.D⟩] ++ [below s.sp (P.c.H.fbytes + P.c.H.F)]) s' →
      (∀ k0 text, k0.length = P.c.H.B → k0.length + text.length < 2 ^ 64 →
        P.hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .a2 = BitVec.ofNat 64 (P.c.H.B + text.length) →
        P.hH.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o P.c.H.D = hmacBlockKey P.hH.SH.H k0 text) → Q s') :
    WP isa (.call P.c.hfN P.c.H.finalize) s Q := by
  have hS := P.hH.hS; have hD := P.hH.hD; have hB := P.hH.hB
  have hl := P.hH.lay
  have c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  have c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  have c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
  have c3 : s.callEntry.gpr .a3 = o := (State.callEntry_gpr _ (by decide)).trans h.a3
  refine WP.callAny (k := hfK P.c.H P.hH.SH) (hf_ok P) (rd := [⟨ou, P.hH.SH.stateBytes⟩])
    (wr := [⟨inn, P.hH.SH.stateBytes⟩, ⟨o, P.hH.SH.digestBytes⟩]) h.pre (by rw [hS, hD]; exact h.hc)
    (by rw [hS, hD]; exact h.hw) ?_ (by have := hf_sdepth P; have := hl.fbytes; have := hl.F; omega)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3,
    hD, hB] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hS, hD] at hf
  exact Frame.below_mono hf (hf_sdepth P) (by have := hl.fbytes; have := hl.F; omega)

/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem hf_rel {Q : State → State → Prop} {inn ou o : Addr}
    (h : ∀ s s', Q s s' → HfArgs P s inn ou o ∧ HfArgs P s' inn ou o ∧ s.sp = s'.sp ∧
      s.gpr .a2 = s'.gpr .a2) :
    RelCT isa Q (.call P.c.hfN P.c.H.finalize) fun _ _ => True := by
  have hS := P.hH.hS; have hD := P.hH.hD
  refine RelCT.call (hf_ok P) P.hfCt [⟨ou, P.hH.SH.stateBytes⟩]
    [⟨inn, P.hH.SH.stateBytes⟩, ⟨o, P.hH.SH.digestBytes⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e2⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hS, hD]; exact a'.hw⟩
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a3, a'.a3, e2]
  simp only [true_and]
  exact e

end

/-- What a call of the streaming `update` needs: the state at `st` and the
`len` bytes at `dat`. -/
structure UpdArgs (P : Rfc) (s : State) (st dat : Addr) (len : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a2 : s.gpr .a2 = dat
  a3 : (s.gpr .a3).toNat = len
  d : Region.Disjoint ⟨dat, len⟩ ⟨st, P.c.H.S⟩
  al : s.sp.toNat % 16 = 0
  sp : P.c.H.F ≤ s.sp.toNat
  b_s : (below s.sp P.c.H.F).Disjoint ⟨st, P.c.H.S⟩
  b_d : (below s.sp P.c.H.F).Disjoint ⟨dat, len⟩
  hc : RISCV64.Covers ([⟨dat, len⟩] ++ [⟨st, P.c.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨st, P.c.H.S⟩] s.wr

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call {P : Rfc} {s : State} {st dat : Addr} {len : Nat} (h : UpdArgs P s st dat len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, P.c.H.S⟩] ++ [below s.sp P.c.H.F]) s' →
      (∀ m, P.hH.SH.Repr s.mem st m → s.gpr .a1 = BitVec.ofNat 64 m.length →
        P.hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa P.c.H.callUpd s Q :=
  P.hH.callUpd_ok h.a0 h.a2 h.a3 h.d h.al h.sp h.b_s h.b_d h.hc h.hw
    fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

end VG.Proof.Ecdsa.Rfc6979.RISCV64
