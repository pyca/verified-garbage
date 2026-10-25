module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Calls
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Spec.Sha256

/-!
# HMAC over any streaming hash function on RISC-V: the hash function

`HashOK H` is what the proofs know of a hash function's streaming functions
`H`: they are verified against `initK`, `updK` and `finK` for the
specification's hash function `SH`, with the sizes of the code; they use at
most `F` bytes of stack below the stack pointer (`sdepth`); a streaming
state that represents whole blocks represents them wherever its hash value
is (`reloc`: its buffer is empty); and what a streaming state represents
depends only on its bytes (`congr`). `callInit_ok`, `callUpd_ok` and
`callFin_ok` are their calls, used as black boxes through their proofs
(`WP.callAny`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- The facts about a hash function's streaming functions. -/
structure HashOK (H : Hash) where
  SH : StreamingHash
  hS : SH.stateBytes = H.S
  hD : SH.digestBytes = H.D
  hB : SH.H.blockSize = H.B
  hb : H.b = 6 ∨ H.b = 7
  hN : 0 < H.N ∧ H.N ≤ 64
  hD0 : 0 < H.D
  hD64 : H.D ≤ 64
  hF : H.F ≤ 1024
  init : ∀ s, (initK H.S SH.Repr).pre s → ∃ t s', Exec isa H.initC s t s' ∧ abiPreserved s s' ∧
    (initK H.S SH.Repr).post s s'
  upd : ∀ s, (updK H.S H.F SH.Repr).pre s → ∃ t s', Exec isa H.updC s t s' ∧ abiPreserved s s' ∧
    (updK H.S H.F SH.Repr).post s s'
  fin : ∀ s, (finK H.S H.F H.D SH.Repr SH.H.hash).pre s → ∃ t s', Exec isa H.finC s t s' ∧
    abiPreserved s s' ∧ (finK H.S H.F H.D SH.Repr SH.H.hash).post s s'
  initSd : sdepth H.initC ≤ H.F
  updSd : sdepth H.updC ≤ H.F
  finSd : sdepth H.finC ≤ H.F
  reloc : ∀ (m m' : Mem) (p q : Addr) (x : List Byte), x.length % H.B = 0 →
    (∀ i < H.N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p x → SH.Repr m' q x
  congr : ∀ (m m' : Mem) (p : Addr) (x : List Byte),
    (∀ i < H.S, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → SH.Repr m p x → SH.Repr m' p x
  hashLen : ∀ x, (SH.H.hash x).length = H.D

namespace HashOK

variable {H : Hash} (hH : HashOK H)

include hH in
theorem hB64 : H.B = 64 ∨ H.B = 128 := by
  rcases hH.hb with h | h <;> simp [Hash.B, h]

include hH in
/-- A callee's frames are in the `F` bytes below the stack pointer. -/
theorem frameF {c : Prog isa} (hd : sdepth c ≤ H.F) {wr : List Region} {sp : Addr} {m m' : Mem}
    (h : Frame (wr ++ [below sp (sdepth c)]) m m') : Frame (wr ++ [below sp H.F]) m m' :=
  Frame.below_mono h hd (by have := hH.hF; omega)

/-- The call of the streaming `init` on the state at `st`. -/
theorem callInit_ok {s : State} {st : Addr} (h0 : s.gpr .a0 = st)
    (hc : Covers [⟨st, H.S⟩] (s.rd ++ s.wr)) (hw : Covers [⟨st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩] ++ [below s.sp H.F]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa H.callInit s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  refine WP.callAny (k := initK H.S hH.SH.Repr) hH.init (rd := []) (wr := [⟨st, H.S⟩]) ?_
    (by simpa using hc) hw ?_ (by have := hH.initSd; have := hH.hF; omega)
  · simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0]
    exact ⟨trivial, trivial⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [initK, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' h₁ h₂ h₃ (frameF hH hH.initSd h₄) hcs hpost

/-- The call of the streaming `update` on the state at `st`, with the `len`
bytes at `dat` and `count` in `a1`. -/
theorem callUpd_ok {s : State} {st dat : Addr} {len : Nat}
    (h0 : s.gpr .a0 = st) (h2 : s.gpr .a2 = dat) (h3 : (s.gpr .a3).toNat = len)
    (hd : Region.Disjoint ⟨dat, len⟩ ⟨st, H.S⟩) (hal : s.sp.toNat % 16 = 0) (hsp : H.F ≤ s.sp.toNat)
    (hs₁ : (below s.sp H.F).Disjoint ⟨st, H.S⟩) (hs₂ : (below s.sp H.F).Disjoint ⟨dat, len⟩)
    (hc : Covers ([⟨dat, len⟩] ++ [⟨st, H.S⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩] ++ [below s.sp H.F]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa H.callUpd s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.gpr .a1 := State.callEntry_gpr _ (by decide)
  have c2 : s.callEntry.gpr .a2 = dat := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : (s.callEntry.gpr .a3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3]
  refine WP.callAny (k := updK H.S H.F hH.SH.Repr) hH.upd (rd := [⟨dat, len⟩])
    (wr := [⟨st, H.S⟩]) ?_ hc hw ?_ (by have := hH.updSd; have := hH.hF; omega)
  · simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c2, c3]
    exact ⟨trivial, trivial, hd, hal, hsp, hs₁, hs₂⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      c3] at hpost
    exact hQ s' h₁ h₂ h₃ (frameF hH hH.updSd h₄) hcs hpost

/-- The call of the streaming `finalize` on the state at `st`, with `count`
in `a1` and its digest to `o`. -/
theorem callFin_ok {s : State} {st o : Addr}
    (h0 : s.gpr .a0 = st) (h2 : s.gpr .a2 = o)
    (hd : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.D⟩) (hal : s.sp.toNat % 16 = 0) (hsp : H.F ≤ s.sp.toNat)
    (hs₁ : (below s.sp H.F).Disjoint ⟨st, H.S⟩) (hs₂ : (below s.sp H.F).Disjoint ⟨o, H.D⟩)
    (hc : Covers [⟨st, H.S⟩, ⟨o, H.D⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, H.S⟩, ⟨o, H.D⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩, ⟨o, H.D⟩] ++ [below s.sp H.F]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .a1 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem o H.D = hH.SH.H.hash m) → Q s') :
    WP isa H.callFin s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.gpr .a1 := State.callEntry_gpr _ (by decide)
  have c2 : s.callEntry.gpr .a2 = o := (State.callEntry_gpr _ (by decide)).trans h2
  refine WP.callAny (k := finK H.S H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin (rd := [])
    (wr := [⟨st, H.S⟩, ⟨o, H.D⟩]) ?_ (by simpa using hc) hw ?_
    (by have := hH.finSd; have := hH.hF; omega)
  · simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c2]
    exact ⟨trivial, trivial, hd, hal, hsp, hs₁, hs₂⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1,
      c2] at hpost
    exact hQ s' h₁ h₂ h₃ (frameF hH hH.finSd h₄) hcs hpost

/-- A streaming state representing whole blocks survives writes outside its
hash value. -/
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {x : List Byte}
    (hx : x.length % H.B = 0) (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) (hr : hH.SH.Repr m p x) :
    hH.SH.Repr m' p x :=
  hH.reloc m m' p p x hx (fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd
    (by have : H.N ≤ 64 := hH.hN.2; show H.N ≤ 2 ^ 64; omega) hi) hr

end HashOK

end VG.Proof.Hmac.Stream.RISCV64
