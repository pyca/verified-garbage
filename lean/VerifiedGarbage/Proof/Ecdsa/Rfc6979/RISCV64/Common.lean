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
public import VerifiedGarbage.Proof.HashTable.RISCV64
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Deterministic ECDSA on RISC-V: the contract, the layout and the calls

The contract the proof of the code for one hash function is written against
(`rfcR`), with the table `hash` holding the addresses of that hash
function's streaming functions (`TabMem`), which an indirect call of the
functions `f` reaches (`TabOK`); what the proof needs of an instance
(`Rfc`): the code's configuration, the hash function's streaming functions
(`TVar`, whose sizes are the configuration's), the shared contract's
instance, and the curve's (`Kit`: its scalars' words, the functions of its
order, and the signature with a given `k` with its constant tables, if
any). The proofs start from the state the frame's body starts in (`s₀`,
with the stack pointer at the frame and `X` bytes of stack below it for the
functions we call), whose precondition is `Pre`; `KR` is what holds from
the end of the prologue on: the regions, the stack pointer, the registers
holding the pointers and the table, our caller's registers in the save
area, and memory outside the frame, `out`, `scratch` and the stack below the
frame (`wrs`).

The calls of the streaming `update` (`HashOK.callUpd_ok`) and of the
signature with a given `k` (the kit's `core_call`): what each needs of the
state it is called from, and what holds when it returns; and, for the
signature's, that two runs of the call with the same arguments leak the
same trace (the kit's `core_rel`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Impl.RsaOaep.RISCV64 (Fns)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (TabMem TabOK)
open VG.Proof.HashTable.RISCV64 (TVar)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The contract -/

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- `sign(out, d, digest, digest_len, scratch, hash)`, with `N` bytes of
stack, for the hash function `H` whose streaming functions an indirect call
of `f` reaches. -/
def rfcR (I : Spec.Ecdsa.Rfc6979.Instance) (H : Hash) (f : Fns) (N : Nat) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .a1, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .a2, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    let tab : Region := ⟨s.gpr .a5, 40⟩
    let stk : Region := below s.sp N
    s.rd = [d, digest, tab] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ s.sp.toNat % 16 = 0 ∧ N ≤ s.sp.toNat ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .a0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat % 8 = 0 ∧
      tab.Disjoint out ∧ tab.Disjoint scratch ∧ stk.Disjoint tab ∧
      (s.gpr .a5).toNat % 8 = 0 ∧ (s.gpr .a5).toNat + 40 ≤ 2 ^ 64 ∧
      TabMem H s.syms (s.gpr .a5) s.mem ∧ TabOK H f s.syms
  post s s' :=
    match (result I s.mem (s.gpr .a1) (s.gpr .a2)).1 with
    | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * I.ecdsa.curve.len) = Spec.Ecdsa.encode I.ecdsa.curve rs
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * I.ecdsa.curve.len) =
          List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.syms H.initN = s₂.syms H.initN ∧ s₁.syms H.updN = s₂.syms H.updN ∧ s₁.syms H.finN = s₂.syms H.finN ∧
    (result I s₁.mem (s₁.gpr .a1) (s₁.gpr .a2)).2 = (result I s₂.mem (s₂.gpr .a1) (s₂.gpr .a2)).2

/-- `rfcR` with the tables `K` the signature with a given `k` reads
(`abi.withConsts`): `rfcR` for the state without them, and what they add. -/
def rfcRC (K : List (String × List (BitVec 64))) (I : Spec.Ecdsa.Rfc6979.Instance) (H : Hash) (f : Fns)
    (N : Nat) : Contract isa where
  pre s := (rfcR I H f N).pre (stripConsts K s) ∧ ConstsOk K N s
  post := (rfcR I H f N).post
  pub s₁ s₂ := (rfcR I H f N).pub s₁ s₂ ∧ ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-! ## The instance -/

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

/-- What a call of the signature with a given `k`, of `Q` bytes scalars,
needs: `out` at `o`, `d`, the digest (`G` bytes) and `k` at `d`, `g` and
`k`, the working space at `w`, and the tables `K` apart from what it writes. -/
structure CoreArgsG (Q G : Nat) (K : List (String × List (BitVec 64))) (s : State) (o d g k w : Addr) : Prop where
  a0 : s.gpr .a0 = o
  a1 : s.gpr .a1 = d
  a2 : s.gpr .a2 = g
  a3 : s.gpr .a3 = k
  a4 : s.gpr .a4 = w
  d_ow : Region.Disjoint ⟨o, 2 * Q⟩ ⟨w, 8192⟩
  d_dw : Region.Disjoint ⟨d, Q⟩ ⟨w, 8192⟩
  d_gw : Region.Disjoint ⟨g, G⟩ ⟨w, 8192⟩
  d_kw : Region.Disjoint ⟨k, Q⟩ ⟨w, 8192⟩
  no : o.toNat + 2 * Q ≤ 2 ^ 64
  nd : d.toNat + Q ≤ 2 ^ 64
  ng : g.toNat + G ≤ 2 ^ 64
  nk : k.toNat + Q ≤ 2 ^ 64
  nw : w.toNat + 8192 ≤ 2 ^ 64
  wa : w.toNat % 8 = 0
  held : Abi.constsHeld s.mem (fun name => s.syms name) K
  tfit : ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ 64
  tal : ∀ t ∈ constRegs K s, t.base.toNat % 64 = 0
  t_o : ∀ t ∈ constRegs K s, t.Disjoint ⟨o, 2 * Q⟩
  t_w : ∀ t ∈ constRegs K s, t.Disjoint ⟨w, 8192⟩
  hc : RISCV64.Covers ([⟨d, Q⟩, ⟨g, G⟩, ⟨k, Q⟩] ++ constRegs K s ++ [⟨o, 2 * Q⟩, ⟨w, 8192⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨o, 2 * Q⟩, ⟨w, 8192⟩] s.wr

/-- `CoreArgsG` for a digest of `Q` bytes. -/
abbrev CoreArgs (Q : Nat) := CoreArgsG Q Q

/-- The signature of the digest at `g` (`G` bytes) with the key at `d` and
the secret number at `k`, of `Q` bytes each, as the specification computes
it: the secret number the `Q` bytes' number shifted right by `sh` bits. -/
abbrev sgOf (E : Spec.Ecdsa.Instance) (Q G sh : Nat) (m : Mem) (d g k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith E.curve (Spec.Weierstrass.ofBytes (bytesAt m d Q))
    (Spec.Ecdsa.hashToInt E.curve (bytesAt m g G)) (Spec.Weierstrass.ofBytes (bytesAt m k Q) >>> sh)

/-- What the proof needs of the curve: its scalars' 64-bit words, its ECDSA
instance, the functions of its order `n` (whose addition `bits2octets`
calls), and the signature with a given `k`, the tables it reads, its
correctness and its constant time by call. -/
structure Kit where
  nw : Nat
  Q : Nat := 8 * nw
  E : Spec.Ecdsa.Instance
  FN : VG.Impl.Weierstrass.RISCV64.Field
  FNok : VG.Proof.Weierstrass.RISCV64.FieldOk FN
  FNk : FN.S.k = nw
  FNm : FN.S.m = E.curve.n
  len : E.curve.len = Q
  /-- The bits of a scalar's `Q` bytes that are not its number's. -/
  sh : Nat := 0
  nbits : Spec.Ecdsa.nBits E.curve + sh = 8 * Q
  sh8 : sh < 8
  two : sh = 0 → 2 ^ (8 * Q) < 2 * E.curve.n
  nw9 : 4 ≤ nw ∧ nw ≤ 9
  Qw : Q = 8 * nw ∨ (nw = 4 ∧ Q = 28) ∨ (nw = 4 ∧ Q = 24) ∨ (nw = 9 ∧ Q = 66)
  /-- The bytes of the digest the signature reads. -/
  G : Nat := Q
  coreC : Prog isa
  K : List (String × List (BitVec 64))
  core_call : ∀ {nm : String} {s : State} {o d g k w : Addr}, CoreArgsG Q G K s o d g k w →
    ∀ {R : State → Prop}, (∀ s', After s [⟨o, 2 * Q⟩, ⟨w, 8192⟩] s' →
      (match sgOf E Q G sh s.mem d g k with
        | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem o (2 * Q) = Spec.Ecdsa.encode E.curve rs
        | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem o (2 * Q) = List.replicate (2 * Q) 0) → R s') →
    WP isa (.call nm coreC) s R
  core_rel : ∀ {nm : String} {R : State → State → Prop} {o d g k w : Addr} {f : String → BitVec 64},
    (∀ s s', R s s' → CoreArgsG Q G K s o d g k w ∧ CoreArgsG Q G K s' o d g k w ∧ s.sp = s'.sp ∧
      ∀ c ∈ K, s.syms c.1 = f c.1 ∧ s'.syms c.1 = f c.1) →
    RelCT isa R (.call nm coreC) fun _ _ => True

/-- What the proof needs of an instance: a curve's kit with the code for a
hash function's sizes, and that hash function's streaming functions (`w`). -/
structure Rfc where
  c : Cfg
  w : TVar
  hDw : c.D = w.H.D
  hBw : c.B = w.H.B
  I : Spec.Ecdsa.Rfc6979.Instance
  kit : Kit
  hE : I.ecdsa = kit.E
  hHash : I.hash = w.l.ok.SH.H
  hD : I.hashLen = c.D
  hnw : c.nw = kit.nw
  hQ : c.Q = kit.Q
  /-- The signature reads the digest's `D` bytes if the scalars are longer
  (`wide`), else their `Q` bytes, with their whole bytes as `k`. -/
  hG : kit.G = if c.wide then c.D else kit.Q
  hsh : c.wide = false → kit.sh = 0
  hQD : kit.Q ≤ c.D + 8
  hD64 : c.D ≤ 64
  hD4 : c.D % 4 = 0
  hS : w.H.S ≤ 192
  hct : c.tries = I.tries
  hT : 1 ≤ c.tries
  hT' : c.tries < 2048
  hFN : c.FN = kit.FN
  hcC : c.coreC = kit.coreC

namespace Rfc

variable (P : Rfc)

/-- The hash function's streaming functions, and what the proofs know of them. -/
abbrev H : Hash := P.w.H
abbrev hH : HashOK P.H := P.w.l.ok

/-- The bytes of stack the functions we call use below the frame: the most
the streaming functions' frames may take (`FitsF`). -/
def X (_P : Rfc) : Nat := 208

/-- The stack the function uses. -/
def N : Nat := P.c.frB + P.X

end Rfc

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev out : Addr := s₀.gpr .a0
abbrev dk : Addr := s₀.gpr .a1
abbrev dg : Addr := s₀.gpr .a2
abbrev scr : Addr := s₀.gpr .a4
abbrev tab : Addr := s₀.gpr .a5
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
abbrev Rfc.Q (P : Rfc) : Nat := P.kit.Q

/-- `out`, `d`, and the frame. -/
abbrev outR (P : Rfc) (s₀ : State) : Region := ⟨out s₀, 2 * P.Q⟩
abbrev dR (P : Rfc) (s₀ : State) : Region := ⟨dk s₀, P.Q⟩
abbrev frR (P : Rfc) (s₀ : State) : Region := ⟨s₀.sp, P.c.frB⟩

/-- The digest, and the table. -/
abbrev dgR (P : Rfc) (s₀ : State) : Region := ⟨dg s₀, P.c.D⟩
abbrev tabR (s₀ : State) : Region := ⟨tab s₀, 40⟩
/-- The stack below the frame the functions we call use. -/
abbrev stk (P : Rfc) (s₀ : State) : Region := below s₀.sp P.X
/-- Everything the code writes. -/
abbrev wrs (P : Rfc) (s₀ : State) : List Region := [frR P s₀, outR P s₀, scrR s₀, stk P s₀]

/-- The state the frame's body starts in. -/
structure Pre (P : Rfc) (s₀ : State) : Prop where
  rd : s₀.rd = [dR P s₀, dgR P s₀, tabR s₀] ++ constRegs P.kit.K s₀
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
  ng : (dg s₀).toNat + P.c.D ≤ 2 ^ 64
  nc : (scr s₀).toNat + 8192 ≤ 2 ^ 64
  ca : (scr s₀).toNat % 8 = 0
  /-- The tables: their words, where, apart from what the code writes. -/
  held : Abi.constsHeld s₀.mem (fun name => s₀.syms name) P.kit.K
  tal : ∀ t ∈ constRegs P.kit.K s₀, t.base.toNat % 64 = 0
  tfit : ∀ t ∈ constRegs P.kit.K s₀, t.base.toNat + t.len ≤ 2 ^ 64
  t_w : ∀ t ∈ constRegs P.kit.K s₀, ∀ r ∈ wrs P s₀, t.Disjoint r
  /-- The table: apart from what the code writes, aligned, holding the hash
  function's streaming functions, which an indirect call of `f` reaches. -/
  b_w : ∀ r ∈ wrs P s₀, (tabR s₀).Disjoint r
  ba : (tab s₀).toNat % 8 = 0
  bn : (tab s₀).toNat + 40 ≤ 2 ^ 64
  bm : TabMem P.H s₀.syms (tab s₀) s₀.mem
  bo : TabOK P.H P.c.f s₀.syms

/-! ## The sizes -/

/-- The sizes the proofs use. -/
structure Sz (P : Rfc) : Prop where
  N : 0 < P.H.N ∧ P.H.N ≤ 64
  B : P.c.B = 64 ∨ P.c.B = 128
  S : P.H.S = P.H.N + P.c.B
  S192 : P.H.S ≤ 192
  D : P.Q ≤ P.c.D + 8 ∧ P.c.D ≤ 64
  /-- The scalars are longer than the hash's output exactly if `wide`. -/
  W : P.c.wide = false ↔ P.Q ≤ P.c.D
  Q : 24 ≤ P.Q ∧ P.Q ≤ 72 ∧ P.c.Q = P.Q ∧
    (P.c.fH + 8 * P.kit.nw * P.c.nums ≤ P.c.frB ∧ P.c.fH + 8 * P.kit.nw ≤ P.c.frB ∧
      P.c.frB ≤ P.c.fH + 16 * P.kit.nw + 15 ∧ P.c.frB % 16 = 0) ∧
    P.Q ≤ 8 * P.kit.nw ∧ 8 * P.kit.nw ≤ P.Q + 8 ∧ (32 ≤ 8 * P.kit.nw ∧ 8 * P.kit.nw ≤ 72)
  nums : P.c.nums = if P.c.wide then 2 else 1
  H : 128 + P.c.D + 1 ≤ P.c.fH ∧ 192 ≤ P.c.fH ∧ P.c.fH ≤ 208 ∧ P.c.fH % 8 = 0
  HF : P.H.F ≤ 208
  X : P.H.F ≤ P.X ∧ P.X = 208
  DB : P.H.D = P.c.D ∧ P.H.B = P.c.B ∧ 0 < P.c.D

/-- The scalars are no longer than the hash's output exactly if not `wide`. -/
theorem Rfc.wide_iff (P : Rfc) : P.c.wide = false ↔ P.kit.Q ≤ P.c.D := by
  simp only [Cfg.wide, P.hQ, decide_eq_false_iff_not, Nat.not_lt]

/-- If not `wide`, the scalars' bytes are all their number's. -/
theorem Rfc.nbits0 (P : Rfc) (hw : P.c.wide = false) : Spec.Ecdsa.nBits P.kit.E.curve = 8 * P.kit.Q := by
  have := P.kit.nbits
  rw [P.hsh hw] at this
  omega

/-- The digest's bytes the signature reads. -/
theorem Rfc.G0 (P : Rfc) (hw : P.c.wide = false) : P.kit.G = P.kit.Q := by
  rw [P.hG, hw]; rfl

theorem Rfc.GW (P : Rfc) (hw : P.c.wide = true) : P.kit.G = P.c.D := by
  rw [P.hG, hw]; rfl

theorem sizes (P : Rfc) : Sz P := by
  have hB := P.hH.hB64
  have := P.kit.nw9
  have := P.kit.Qw
  have hD := P.hD64
  have hDQ := P.hQD
  have hnw := P.hnw
  have hDw := P.hDw
  have hBw := P.hBw
  have hD0 := P.hH.hD0
  have hF : P.H.F ≤ 208 := P.w.l.fits
  have hfH : (P.c.fH = 192 ∧ P.c.D < 64) ∨ (P.c.fH = 208 ∧ ¬ P.c.D < 64) := by
    unfold Cfg.fH; split <;> simp_all
  have hnu : P.c.nums = 1 ∨ P.c.nums = 2 := by unfold Cfg.nums; split <;> simp
  refine ⟨P.hH.hN, by rw [hBw]; exact hB, by rw [hBw], P.hS, ⟨hDQ, hD⟩, P.wide_iff, ⟨by simp only [Rfc.Q]; omega,
    by simp only [Rfc.Q]; omega, by simp only [Rfc.Q, P.hQ], ?_, by simp only [Rfc.Q]; omega,
    by simp only [Rfc.Q]; omega, by omega⟩, rfl, by omega, hF, ⟨hF, rfl⟩, ⟨hDw.symm, hBw.symm, by omega⟩⟩
  simp only [Cfg.frB, hnw]
  rcases hnu with h | h <;> rw [h] <;> omega

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
  ⟨_, fr_wr hp hwr, Offset.contains_base _ h (by have := (sizes P).Q; have := (sizes P).H; omega)⟩

theorem in_fr' {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ P.c.frB) :
    InRegions (s.rd ++ s.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (fr_wr hp hwr), Offset.contains_base _ h (by have := (sizes P).Q; have := (sizes P).H; omega)⟩

/-- The frame is apart from the stack below it. -/
theorem f_s : (frR P s₀).Disjoint (stk P s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spX; have := s₀.sp.isLt; omega)

/-- The stack below the stack pointer, within `stk`. -/
theorem below_stk {n : Nat} (hn : n ≤ P.X) : Region.Sub (below s₀.sp n) (stk P s₀) :=
  below_sub hn (by have := hp.spX; have := s₀.sp.isLt; omega)

end

/-! ## What every piece keeps -/

/-- The callee-saved registers the code never writes. -/
abbrev nvRegs : List Reg := [.s7, .s8, .s9, .s10, .s11]

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
  s6 : s.gpr .s6 = tab s₀
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r
  saved : Spill.Saved s₀.sp s₀.gpr saved s.mem
  frame : Frame (wrs P s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s6, .s7, .s8, .s9, .s10, .s11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved := by decide

theorem saved_fits : Spill.Fits saved := by
  refine ⟨fun q hq => ?_, by decide⟩
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem saved_in : ∀ q ∈ saved, 0 ≤ q.2 ∧ q.2 + 8 ≤ 0 + 64 := by
  intro q hq
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {P : Rfc} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR P s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, Region.Disjoint (svR s₀) r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs P s₀, Region.Sub r r') : KR P s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.s0, (hg _ (by simp)).trans h.s1,
    (hg _ (by simp)).trans h.s2, (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s4,
    (hg _ (by simp)).trans h.s6, fun r hr => (hg r (by revert r; decide)).trans (h.nv r hr),
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
  have sv : Region.Sub (svR s₀) (frR P s₀) := part_sub (by have := (sizes P).Q; have := (sizes P).H; omega)
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | h | ⟨n, rfl, hn⟩
  · exact ⟨part_disj (s₀ := s₀) (.inl h₁) (by have := (sizes P).Q; have := (sizes P).H; omega) (by have := (sizes P).Q; have := (sizes P).H; omega),
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
    · exact hp.b_d.symm) (by have := (sizes P).Q; have := (sizes P).H; omega)

theorem KR.dgBytes (hp : Pre P s₀) {s : State} (hk : KR P s₀ s) {n : Nat} (hn : n ≤ P.c.D) :
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

end VG.Proof.Ecdsa.Rfc6979.RISCV64
