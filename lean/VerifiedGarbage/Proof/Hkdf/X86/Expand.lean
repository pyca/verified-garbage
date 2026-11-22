module

public import VerifiedGarbage.Proof.Hkdf.X86.Env
public import VerifiedGarbage.Proof.Hkdf.X86.Key
public import VerifiedGarbage.Proof.Hkdf.X86.Extract
public import VerifiedGarbage.Proof.Hkdf.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Hkdf.X86

/-!
# HKDF on x86 (32-bit): `vg_hkdf_expand`, correct and constant time

The contract the proof is written against (`expandR`), for the table `hmac`
of one variant `w` (`HVar`), whose functions an indirect call of `f`'s
reaches: `expand(key, info, info_len, out, out_len, hmac)` writes
HKDF-Expand's `out_len` bytes to `out`, for every pseudorandom key the
states at `key` are keyed with (`Spec.Hkdf.Keyed`). In its frame (`eFr`
bytes: our caller's registers, `D`, `B`, the counter, the bytes of `out`
left, the next byte of `out`, the length of `T(i - 1)` (`Words`), the
working state, `T(i)`, the counter's byte, then the working space), the
entry copies `D` and `B` from the table and sets the counters (`etab_ok`,
from which on `EI 0` holds). Each block (`block_ok`) copies the inner state
at `key` to the working state, absorbs `T(i - 1)`, `info` and the counter,
finalizes with the outer state at `key + 192` into `T(i)` in the frame, and
copies its first `min(D, rem)` bytes to `out`; before block `k + 1`, `out`'s
first `min(k D, L)` bytes are `T(1) ‖ … ‖ T(k)`'s (`EI k`). The blocks run
while bytes of `out` are left (`loop_ok`). Each stage's predicate (`Pr`)
says what both of two runs with the same layout have, so the stages are
related in two runs by the same lemmas (`expand_ct`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86

open VG VG.X86 VG.X86.Wp
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.HmacTable.X86 (HVar TabOK TabMem)
open VG.Proof.Pbkdf2.Whole.X86 (HfArgs)
open VG.Proof.Pbkdf2.Stream.X86 (UpdArgs)

/-! ## The contract -/

/-- The stack `vg_hkdf_expand` uses: its frame, and the 76 bytes below it the
calls of `finalize` use. -/
def eStack : Nat := Impl.Hkdf.X86.eFr + 76

/-- `expand(key, info, info_len, out, out_len, hmac)`, with `N` bytes of
stack, for the table `hmac` of `w`, whose functions an indirect call of `f`'s
reaches, with the addresses of the functions `ns` public. -/
def expandR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
    let info : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let out : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let tab : Region := ⟨(arg s 5).setWidth 64, 24⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 24 ≤ 2 ^ 32 ∧
      s.rd = [key, info, tab] ∧ s.wr = [out, args] ∧
      key.Disjoint out ∧ info.Disjoint out ∧ out.Disjoint tab ∧ out.Disjoint args ∧ ret.Disjoint out ∧
      stk.Disjoint key ∧ stk.Disjoint info ∧ stk.Disjoint out ∧ stk.Disjoint tab ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 24 ≤ 2 ^ 32 ∧
      (arg s 4).toNat ≤ 255 * w.F.H.D ∧ TabFacts w f s (arg s 5)
  post s s' := ∀ prk, Spec.Hkdf.Keyed w.ok.hH.SH s.mem ((arg s 0).setWidth 64) prk →
    Spec.Hkdf.expand w.ok.hH.SH.H w.F.H.D prk (Spec.Sha256.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
      (arg s 4).toNat = some (Spec.Sha256.bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-! ## The layout -/

/-- `expand`'s frame: 2172 bytes, 76 below it, six arguments, the table the last. -/
def eSh : Sh := ⟨Impl.Hkdf.X86.eFr, 76, 6, 5⟩

/-- The layout of a call from `s`. -/
def layE (w : HVar) (s : State) : Lay eSh where
  E := s.gpr .esp
  a i := if i < 6 then arg s i else 0
  W := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  rd := [⟨(arg s 0).setWidth 64, 384⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 5).setWidth 64, 24⟩]
  wr := [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩]
  fa := faOf w s

/-- What `expand` needs of the layout besides `Lay.Ok`: the states' and
`info`'s places, `out`, and the variant's sizes. -/
structure EOk (w : HVar) (L : Lay eSh) : Prop where
  hw : HOk w
  W : L.W = ⟨(L.a 3).setWidth 64, (L.a 4).toNat⟩
  kRd : (⟨(L.a 0).setWidth 64, 384⟩ : Region) ∈ L.rd
  iRd : (⟨(L.a 1).setWidth 64, (L.a 2).toNat⟩ : Region) ∈ L.rd
  kW : Region.Disjoint ⟨(L.a 0).setWidth 64, 384⟩ L.W
  iW : Region.Disjoint ⟨(L.a 1).setWidth 64, (L.a 2).toNat⟩ L.W
  kK : L.STK.Disjoint ⟨(L.a 0).setWidth 64, 384⟩
  kI : L.STK.Disjoint ⟨(L.a 1).setWidth 64, (L.a 2).toNat⟩
  nk : (L.a 0).toNat + 384 ≤ 2 ^ 32
  ni : (L.a 1).toNat + (L.a 2).toNat ≤ 2 ^ 32
  no : (L.a 3).toNat + (L.a 4).toNat ≤ 2 ^ 32
  ol : (L.a 4).toNat ≤ 255 * w.F.H.D

theorem econsts : Impl.Hkdf.X86.eD = 16 ∧ Impl.Hkdf.X86.eB = 20 ∧ Impl.Hkdf.X86.eCnt = 24 ∧
    Impl.Hkdf.X86.eRem = 28 ∧ Impl.Hkdf.X86.eOut = 32 ∧ Impl.Hkdf.X86.eTl = 36 ∧ Impl.Hkdf.X86.eW = 40 ∧
    Impl.Hkdf.X86.eT = 232 ∧ Impl.Hkdf.X86.eC = 296 ∧ Impl.Hkdf.X86.eWork = 300 ∧ eSh.FB = 2172 ∧ eSh.cb = 76 ∧
    eSh.NA = 6 ∧ eSh.N = 2248 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {w : HVar} {f : Fns} {ns : List String}

theorem layE_a {s : State} {i : Nat} (hi : i < 6) : (layE w s).a i = arg s i := by
  simp only [layE, hi, ite_true]

/-- The layout of a call meeting the contract. -/
theorem layE_ok {s : State} (hw : HOk w) (hp : (expandR w f ns eStack).pre s) :
    (layE w s).Ok ∧ EOk w (layE w s) := by
  obtain ⟨hsp, htop, hrd, hwr, ko, io, ot, oa, ro, kk, ki, kot, kt, nk, ni, no, nt, ol, -⟩ := hp
  have hB : (layE w s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 eSh.N := B_eq' hsp
  have eK : (layE w s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 eStack, eStack⟩ := by
    show (⟨(layE w s).B, eSh.N⟩ : Region) = _; rw [hB]; rfl
  have eR : (layE w s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show (⟨(layE w s).B + BitVec.ofNat 64 eSh.N, 4⟩ : Region) = _; rw [hB, BitVec.sub_add_cancel]
  have eA : (layE w s).ARGS = ⟨argAddr s 0, 24⟩ := by
    show (⟨(layE w s).B + BitVec.ofNat 64 (eSh.N + 4), 4 * 6⟩ : Region) = _
    rw [hB, ← Offset.add_add ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 eSh.N) eSh.N 4, BitVec.sub_add_cancel]
    show (⟨(s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4, 24⟩ : Region) =
      ⟨(s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 24⟩
    rw [show 4 + 4 * 0 = 4 from rfl, ← addr, addr_eq (by omega_arith)]
  have a0 := layE_a (w := w) (s := s) (i := 0) (by decide)
  have a1 := layE_a (w := w) (s := s) (i := 1) (by decide)
  have a2 := layE_a (w := w) (s := s) (i := 2) (by decide)
  have a3 := layE_a (w := w) (s := s) (i := 3) (by decide)
  have a4 := layE_a (w := w) (s := s) (i := 4) (by decide)
  refine ⟨⟨hsp, by show (s.gpr .esp).toNat + 4 + 4 * 6 ≤ 2 ^ 32; omega_arith, by decide, by decide, by decide,
    by decide, by decide, ?_, by rw [eK]; exact kot, by rw [eR]; exact ro, by rw [eA]; exact oa.symm, nt, ot.symm,
    by rw [eK]; exact kt.symm, ?_, ?_, ?_⟩,
    ⟨hw, by rw [a3, a4]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show (BitVec.setWidth 64 (arg s 3)).toNat + (arg s 4).toNat ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega_arith)]; exact no
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  · rw [eA]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  · exact List.mem_cons_self
  · rw [a0]; exact List.mem_cons_self
  · rw [a1, a2]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [a0]; exact ko
  · rw [a1, a2]; exact io
  · rw [eK, a0]; exact kk
  · rw [eK, a1, a2]; exact ki
  · rw [a0]; exact nk
  · rw [a1, a2]; exact ni
  · rw [a3, a4]; exact no
  · rw [a4]; exact ol

/-- What the contract says on entry, with the layout. -/
theorem entryE {s : State} (hp : (expandR w f ns eStack).pre s) : Entry ⟨w, f⟩ (layE w s) s := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, tok, tm, td, tb⟩ := hp
  exact ⟨rfl, hrd, hwr, fun i hi => by have hi' : i < 6 := hi; simp only [layE, hi', ite_true],
    tok, tm, td, tb, fun n hn => by simp only [layE, faOf, hn, ite_true]⟩

end

/-! ## The loop's invariant -/

section
variable (w : HVar)

/-- `out_len`. -/
abbrev olen (L : Lay eSh) : Nat := (L.a 4).toNat
/-- The length of `T(k)`: none for `T(0)`, `D` after. -/
abbrev pl (k : Nat) : Nat := if k = 0 then 0 else w.F.H.D
/-- The bytes of `out` written after `k` blocks. -/
abbrev done (L : Lay eSh) (k : Nat) : Nat := min (k * w.F.H.D) (olen L)
/-- The frame's word at `o`. -/
abbrev fw (L : Lay eSh) (o : Nat) (m : Mem) : BitVec 32 := m.readW (L.B + BitVec.ofNat 64 (eSh.cb + o)) 32
/-- `info`. -/
abbrev infoOf (L : Lay eSh) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ ((L.a 1).setWidth 64) (L.a 2).toNat
/-- The pseudorandom keys the states at `key` are keyed with. -/
abbrev Keyd (L : Lay eSh) (m₀ : Mem) (prk : List Byte) : Prop :=
  Spec.Hkdf.Keyed w.ok.hH.SH m₀ ((L.a 0).setWidth 64) prk

/-- Our variables in the frame, during block `k + 1` (or before it). -/
structure Words (k : Nat) (L : Lay eSh) (m : Mem) : Prop where
  d : fw L Impl.Hkdf.X86.eD m = BitVec.ofNat 32 w.F.H.D
  b : fw L Impl.Hkdf.X86.eB m = BitVec.ofNat 32 w.F.H.B
  cnt : fw L Impl.Hkdf.X86.eCnt m = BitVec.ofNat 32 (k + 1)
  rem : fw L Impl.Hkdf.X86.eRem m = BitVec.ofNat 32 (olen L - done w L k)
  outp : fw L Impl.Hkdf.X86.eOut m = L.a 3 + BitVec.ofNat 32 (done w L k)
  tl : fw L Impl.Hkdf.X86.eTl m = BitVec.ofNat 32 (pl w k)

/-- `out`'s first `done k` bytes, for each pseudorandom key. -/
abbrev OB (k : Nat) (L : Lay eSh) (m₀ m : Mem) : Prop :=
  ∀ prk, Keyd w L m₀ prk → Spec.Sha256.bytesAt m ((L.a 3).setWidth 64) (done w L k) =
    (Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf L m₀) k [] 1).take (done w L k)

/-- `T(k)` in the frame, for each pseudorandom key. -/
abbrev TB (k : Nat) (L : Lay eSh) (m₀ m : Mem) : Prop :=
  ∀ prk, Keyd w L m₀ prk → Spec.Sha256.bytesAt m ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT).setWidth 64) (pl w k) =
    Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k

/-- The working state represents `K₀ ⊕ ipad`, then `msg`, for each
pseudorandom key the states are keyed with. -/
abbrev WS (L : Lay eSh) (m₀ m : Mem) (msg : List Byte → List Byte) : Prop :=
  ∀ prk, Keyd w L m₀ prk → w.ok.hH.SH.Repr m ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW).setWidth 64)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey w.ok.hH.SH.H prk) Spec.Hmac.ipad ++ msg prk)

/-- Before block `k + 1`: our variables, `out`'s first bytes, `T(k)`, and
ZF set when no bytes of `out` are left. -/
def EI (k : Nat) : Pr eSh := fun L m₀ u =>
  EOk w L ∧ Words w k L u.mem ∧ OB w k L m₀ u.mem ∧ TB w k L m₀ u.mem ∧
    u.zf = some (BitVec.ofNat 32 (olen L - done w L k) == 0)

/-- During block `k + 1`, while bytes of `out` are left. -/
def BI (k : Nat) : Pr eSh := fun L m₀ u =>
  EOk w L ∧ k * w.F.H.D < olen L ∧ Words w k L u.mem ∧ OB w k L m₀ u.mem ∧ TB w k L m₀ u.mem

end

section
variable {w : HVar} {f : Fns} {L : Lay eSh} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32}

/-- Our variables, kept by writes apart from them. -/
theorem Words.keep {k : Nat} {m m' : Mem} (h : Words w k L m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩ r) : Words w k L m' := by
  have hcb : eSh.cb = 76 := rfl
  have e : ∀ o, 16 ≤ o → o + 4 ≤ 40 → fw L o m' = fw L o m := fun o h₁ h₂ =>
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩)
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)
  exact ⟨(e _ (by decide) (by decide)).trans h.d, (e _ (by decide) (by decide)).trans h.b,
    (e _ (by decide) (by decide)).trans h.cnt, (e _ (by decide) (by decide)).trans h.rem,
    (e _ (by decide) (by decide)).trans h.outp, (e _ (by decide) (by decide)).trans h.tl⟩

/-- The bytes of a region apart from `rs` are kept. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- Our variables, as a region of the frame. -/
theorem vars_eq (hL : L.Ok) : L.B + BitVec.ofNat 64 (eSh.cb + 16) = (L.F + BitVec.ofNat 32 16).setWidth 64 :=
  (hL.frv (by decide)).symm

/-- Our variables, apart from a part of the frame above them. -/
theorem vars_fr (hL : L.Ok) {o n : Nat} (h₁ : 40 ≤ o) (h₂ : o + n ≤ eSh.FB) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩ ⟨(L.F + BitVec.ofNat 32 o).setWidth 64, n⟩ := by
  rw [vars_eq hL]; exact hL.fr_disj (.inl (by omega_arith)) (by decide) h₂

/-- Our variables, apart from the calls' bytes and `W`. -/
theorem vars_calls (hL : L.Ok) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩ L.CALLS := by
  rw [vars_eq hL]; exact (hL.calls_fr (by decide)).symm

theorem vars_W (hL : L.Ok) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩ L.W := by
  rw [vars_eq hL]; exact hL.fr_W (by decide)

/-- A part of `out` apart from the frame and the calls' bytes. -/
theorem out_sub (hx : EOk w L) {o n : Nat} (h : o + n ≤ olen L) :
    Region.Sub ⟨(L.a 3).setWidth 64 + BitVec.ofNat 64 o, n⟩ L.W := by
  rw [hx.W]; exact Offset.sub_base _ h

theorem out_sub0 (hx : EOk w L) {n : Nat} (h : n ≤ olen L) : Region.Sub ⟨(L.a 3).setWidth 64, n⟩ L.W := by
  rw [hx.W]; exact Region.sub_prefix h

/-- `B + T + info + 1` fits 32 bits, `info` being apart from the stack in
the 32-bit address space. -/
theorem info_lt (hL : L.Ok) (hx : EOk w L) : w.F.H.B + w.F.H.D + (L.a 2).toNat + 1 < 2 ^ 32 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hx.kI (N := 2 ^ 32) (by have := hL.nB; dsimp only; omega_arith)
    (by dsimp only; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (L.a 1).isLt; omega_arith)]; exact hx.ni)
  have hB : w.F.H.B ≤ 128 := w.ok.hH.hBB
  have hD := hx.hw.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, e6⟩ := econsts
  dsimp only at h
  omega_arith

/-- Facts of the sizes, for `omega`. -/
theorem esizes (hx : EOk w L) : w.ok.hH.SH.stateBytes ≤ 192 ∧ w.F.H.S ≤ 192 ∧ w.ok.Wf * 8 ≤ 1872 ∧
    w.ok.hH.Wb ≤ 1872 ∧ w.ok.hH.SH.digestBytes = w.F.H.D ∧ w.F.H.D ≤ 64 ∧ 0 < w.F.H.D ∧ w.F.H.B ≤ 128 := by
  have h := hx.hw
  exact ⟨by rw [w.ok.hH.hS]; exact h.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, w.ok.hH.hD, h.2.2.2.2.2, w.ok.hH.hD0,
    w.ok.hH.hBB⟩


/-! ## Words of the frame -/

theorem fw_write (hL : L.Ok) {m : Mem} {o o' : Nat} (v : BitVec 32) (h : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (h₁ : o + 4 ≤ eSh.FB) (h₂ : o' + 4 ≤ eSh.FB) :
    fw L o' (m.writeW (L.B + BitVec.ofNat 64 (eSh.cb + o)) v) = fw L o' m := by
  have := hL.nB; have := eSh.N_eq
  exact Mem.readW_writeW_sep (Offset.sep L.B (d := eSh.cb + o') (n := 4) (e := eSh.cb + o) (k := 4)
    (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem fw_write8 (hL : L.Ok) {m : Mem} {o o' : Nat} (v : BitVec 8) (h : o + 1 ≤ o' ∨ o' + 4 ≤ o)
    (h₁ : o + 1 ≤ eSh.FB) (h₂ : o' + 4 ≤ eSh.FB) :
    fw L o' (m.writeW (L.B + BitVec.ofNat 64 (eSh.cb + o)) v) = fw L o' m := by
  have := hL.nB; have := eSh.N_eq
  exact Mem.readW_writeW_sep (Offset.sep L.B (d := eSh.cb + o') (n := 4) (e := eSh.cb + o) (k := 1)
    (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem fw_self {m : Mem} {o : Nat} (v : BitVec 32) : fw L o (m.writeW (L.B + BitVec.ofNat 64 (eSh.cb + o)) v) = v :=
  Mem.readW_writeW_self32 _ _ _

/-- Equal lists of bytes, byte by byte. -/
theorem bytesAt_get {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m p n = Spec.Sha256.bytesAt m' q n) {i : Nat} (hi : i < n) :
    m (p + BitVec.ofNat 64 i) = m' (q + BitVec.ofNat 64 i) := by
  have := congrArg (fun l => l[i]?) h
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  exact this

/-! ## The entry -/

/-- `D` and `B` from the table to the frame, and the counters: `EI 0`. -/
theorem etab_ok (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : EOk w L ∧ t.gpr .eax = L.tb) :
    WP isa (.block Impl.Hkdf.X86.expandTab) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ EI w 0 L m₀ u := by
  obtain ⟨hx, hax⟩ := h
  rw [Impl.Hkdf.X86.expandTab, show ([.mov .ecx (.mem (Impl.Pbkdf2.Stream.X86.at_ .eax 16)),
      .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eD) .ecx, .mov .ecx (.mem (Impl.Pbkdf2.Stream.X86.at_ .eax 20)),
      .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eB) .ecx, .mov .ecx (.imm 1), .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eCnt) .ecx,
      .mov .ecx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.eFr 3), .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eOut) .ecx,
      .mov .ecx (.imm 0), .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl) .ecx,
      .mov .ecx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.eFr 4), .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eRem) .ecx,
      .alu .test .ecx (.reg .ecx)] : List Instr) =
    [.mov .ecx (.mem (Impl.Pbkdf2.Stream.X86.at_ .eax 16))] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eD) .ecx] ++
      [.mov .ecx (.mem (Impl.Pbkdf2.Stream.X86.at_ .eax 20))] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eB) .ecx] ++
      [.mov .ecx (.imm 1)] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eCnt) .ecx] ++
      [.mov .ecx (Impl.Hkdf.X86.argM eSh.FB 3)] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eOut) .ecx] ++
      [.mov .ecx (.imm 0)] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl) .ecx] ++
      [.mov .ecx (Impl.Hkdf.X86.argM eSh.FB 4)] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eRem) .ecx] ++
      [.alu .test .ecx (.reg .ecx)] from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (tabld_ok hL hc (d := .ecx) (by decide) hax (o := 16) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (stF_ok hL h₁.ctx .ecx (o := Impl.Hkdf.X86.eD) (by decide) (by decide)) fun u₂ ⟨c₂, m₂, g₂, _⟩ => ?_
  have ax₂ : u₂.gpr .eax = L.tb := by rw [g₂, h₁.keep _ (by decide), hax]
  refine WP.mono (tabld_ok hL c₂ (d := .ecx) (by decide) ax₂ (o := 20) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (stF_ok hL h₃.ctx .ecx (o := Impl.Hkdf.X86.eB) (by decide) (by decide)) fun u₄ ⟨c₄, m₄, g₄, _⟩ => ?_
  refine WP.mono (movi_ok hL c₄ (d := .ecx) (by decide) 1) fun u₅ h₅ => ?_
  refine WP.mono (stF_ok hL h₅.ctx .ecx (o := Impl.Hkdf.X86.eCnt) (by decide) (by decide)) fun u₆ ⟨c₆, m₆, g₆, _⟩ => ?_
  refine WP.mono (arg_ok hL c₆ (d := .ecx) (by decide) (i := 3) (by decide)) fun u₇ h₇ => ?_
  refine WP.mono (stF_ok hL h₇.ctx .ecx (o := Impl.Hkdf.X86.eOut) (by decide) (by decide)) fun u₈ ⟨c₈, m₈, g₈, _⟩ => ?_
  refine WP.mono (movi_ok hL c₈ (d := .ecx) (by decide) 0) fun u₉ h₉ => ?_
  refine WP.mono (stF_ok hL h₉.ctx .ecx (o := Impl.Hkdf.X86.eTl) (by decide) (by decide)) fun u₁₀ ⟨c₁₀, m₁₀, g₁₀, _⟩ => ?_
  refine WP.mono (arg_ok hL c₁₀ (d := .ecx) (by decide) (i := 4) (by decide)) fun u₁₁ h₁₁ => ?_
  refine WP.mono (stF_ok hL h₁₁.ctx .ecx (o := Impl.Hkdf.X86.eRem) (by decide) (by decide))
    fun u₁₂ ⟨c₁₂, m₁₂, g₁₂, _⟩ => ?_
  refine WP.mono (test_ok hL c₁₂ .ecx) fun u ⟨cu, gu, mu, _, zu⟩ => ⟨cu, hx, ?_, ?_, ?_, ?_⟩
  · have M : u.mem = (((((t.mem.writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eD))
        (BitVec.ofNat 32 w.F.H.D)).writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eB))
        (BitVec.ofNat 32 w.F.H.B)).writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eCnt))
        (1 : BitVec 32)).writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eOut)) (L.a 3)).writeW
        (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eTl)) (0 : BitVec 32)).writeW
        (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eRem)) (L.a 4) := by
      rw [mu, m₁₂, h₁₁.mem, m₁₀, h₉.mem, m₈, h₇.mem, m₆, h₅.mem, m₄, h₃.mem, m₂, h₁.mem, h₁₁.val, h₉.val,
        h₇.val, h₅.val, h₃.val, h₁.val, hc.tabD, hc.tabB]
    have hd0 : done w L 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [M]
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide)]; exact fw_self _
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide)]
      exact fw_self _
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide)]; exact fw_self _
    · rw [fw_self, hd0, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_self, hd0, BitVec.add_zero]
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_self]; rfl
  · intro prk _
    simp only [done, Nat.zero_mul, Nat.zero_min, List.take_zero]
    rfl
  · intro prk _; rfl
  · rw [zu, g₁₂, h₁₁.val]
    have hd0 : done w L 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
    rw [hd0, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]


/-! ## A block: the inner state's copy -/

theorem D_le (hx : EOk w L) : w.F.H.D ≤ 64 := hx.hw.2.2.2.2.2

theorem pl_le (k : Nat) : pl w k ≤ w.F.H.D := by unfold pl; split <;> omega_arith

/-- `T(k)` has `pl k` bytes. -/
theorem tBlock_len (prk info : List Byte) (k : Nat) :
    (Proof.Hkdf.tBlock w.ok.hH.SH.H prk info k).length = pl w k := by
  cases k with
  | zero => rfl
  | succ k => exact Proof.Hkdf.tBlock_length _ _ _ w.hlen k

/-- `BI` is kept by writes apart from our variables, `out` and `T`. -/
theorem BI.keep {k : Nat} {t u : State} (h : BI w k L m₀ t) {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hv : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩ r)
    (ho : ∀ r ∈ ws, Region.Disjoint L.W r)
    (ht : ∀ r ∈ ws, Region.Disjoint ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT).setWidth 64, 64⟩ r) :
    BI w k L m₀ u := by
  obtain ⟨hx, hlt, hw, hob, htb⟩ := h
  refine ⟨hx, hlt, hw.keep hf hv, fun prk hk => ?_, fun prk hk => ?_⟩
  · rw [bytes_keep hf (fun r hr => (ho r hr).sub_left (out_sub0 hx (Nat.min_le_right _ _)))
      (Nat.le_trans (Nat.min_le_right _ _) (by show (L.a 4).toNat ≤ 2 ^ 64; have := (L.a 4).isLt; omega_arith))]
    exact hob prk hk
  · rw [bytes_keep hf (fun r hr => (ht r hr).sub_left (Region.sub_prefix (by
      have := pl_le (w := w) k; have := D_le hx; omega_arith))) (by have := pl_le (w := w) k; have := D_le hx; omega_arith)]
    exact htb prk hk

theorem BI.mem {k : Nat} {t t' : State} (h : BI w k L m₀ t) (hm : t'.mem = t.mem) : BI w k L m₀ t' := by
  unfold BI; rw [hm]; exact h

/-- The copy's arguments. -/
def CA (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u =>
  BI w k L m₀ u ∧ u.gpr .esi = L.a 0 ∧ u.gpr .ebx = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW ∧ u.gpr .ecx = 192

theorem copyA_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : BI w k L m₀ t) :
    WP isa (.block Impl.Hkdf.X86.copyA) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ CA w k L m₀ u := by
  rw [Impl.Hkdf.X86.copyA, show ([.mov .esi (Impl.Hkdf.X86.argM Impl.Hkdf.X86.eFr 0), .mov .ebx (.reg .esp),
      .alu .add .ebx (.imm (BitVec.ofNat 32 Impl.Hkdf.X86.eW)), .mov .ecx (.imm 192)] : List Instr) =
    [.mov .esi (Impl.Hkdf.X86.argM eSh.FB 0)] ++ Impl.Hkdf.X86.fr .ebx Impl.Hkdf.X86.eW ++ [.mov .ecx (.imm 192)]
    from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .esi) (by decide) (i := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .ebx) (by decide) Impl.Hkdf.X86.eW) fun u₂ h₂ => ?_
  refine WP.mono (movi_ok hL h₂.ctx (d := .ecx) (by decide) 192) fun u₃ h₃ => ?_
  refine ⟨h₃.ctx, ?_, ?_, ?_, h₃.val⟩
  · have hm : u₃.mem = t.mem := h₃.mem.trans (h₂.mem.trans h₁.mem)
    obtain ⟨hx, hlt, hw, hob, htb⟩ := h
    exact ⟨hx, hlt, by rw [hm]; exact hw, by rw [hm]; exact hob, by rw [hm]; exact htb⟩
  · rw [h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₃.keep _ (by decide), h₂.val]

/-- The working state, the inner state at `key` for each pseudorandom key. -/
def CW (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u => BI w k L m₀ u ∧ WS w L m₀ u.mem fun _ => []

theorem copyW_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : CA w k L m₀ t) :
    WP isa Impl.Hkdf.X86.cpLoop t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ CW w k L m₀ u := by
  obtain ⟨hb, hsi, hbx, hcx⟩ := h
  have hx := hb.1
  obtain ⟨hS, -, -, -, -, -, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have nk := hx.nk; have hFN := hL.FN; have := hL.e0; have := hL.e1
  have hdst : (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW).setWidth 64 = L.FR.base + BitVec.ofNat 64 Impl.Hkdf.X86.eW :=
    hL.frBase (by decide)
  have hrd : InRegions (t.rd ++ t.wr) ((L.a 0).setWidth 64) 192 :=
    ⟨_, List.mem_append_left _ (by rw [hc.rd]; exact hx.kRd),
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)⟩
  have hwr : InRegions t.wr ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW).setWidth 64) 192 := by
    refine ⟨L.FR, by rw [hc.wr]; exact List.mem_cons_self, ?_⟩
    rw [hdst]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hsep : Region.Disjoint ⟨(L.a 0).setWidth 64, 192⟩ ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW).setWidth 64, 192⟩ :=
    ((hx.kK.sub_left (hL.fr_sub (by omega_arith))).symm.sub_left (Region.sub_prefix (by omega_arith)))
  refine WP.mono (cp_ok hL hc (Sv := L.a 0) (Dv := L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) (n := 192)
    (by decide) (by decide) (by omega_arith) (by rw [hL.frN (by omega_arith)]; omega_arith) hrd hwr hsep
    (.inr (.inl (hL.fr_hi (by omega_arith) (by omega_arith)))) hsi hbx hcx) fun u ⟨cu, hf, hbs, _⟩ => ⟨cu, ?_, ?_⟩
  · refine hb.keep hf (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact vars_fr hL (by decide) (by omega_arith)
    · exact (hL.fr_W (by omega_arith)).symm
    · exact hL.fr_disj (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  · intro prk hk
    rw [List.append_nil]
    refine w.ok.hH.repr m₀ u.mem _ _ _ (fun i hi => ?_) hk.1
    rw [w.ok.hH.hS] at hS
    rw [bytesAt_get hbs (by omega_arith)]
    exact hc.bytes (R := ⟨(L.a 0).setWidth 64, 384⟩) hx.kW hx.kK.symm (show 384 ≤ 2 ^ 64 by decide) (show i < 384 by omega_arith)

/-! ## A block: `update`s -/

/-- `WS` for messages equal for every pseudorandom key. -/
theorem WS.congr {m : Mem} {msg msg' : List Byte → List Byte} (h : WS w L m₀ m msg)
    (e : ∀ prk, Keyd w L m₀ prk → msg prk = msg' prk) : WS w L m₀ m msg' := fun prk hk => by
  rw [← e prk hk]; exact h prk hk

/-- `update`'s registers: the working state, holding `lo` bytes, `len` bytes at `d`. -/
def UR (lo d : BitVec 32) (len : Nat) : Pr eSh := fun L _ u =>
  u.gpr .edi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW ∧ u.gpr .esi = lo ∧ u.gpr .eax = 0 ∧ u.gpr .edx = d ∧
    u.gpr .ecx = BitVec.ofNat 32 len ∧ u.gpr .ebp = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork

theorem UR.keep {lo d : BitVec 32} {len : Nat} {t t' : State} (h : UR lo d len L m₀ t)
    (hk : ∀ r, r ≠ .ebx → t'.gpr r = t.gpr r) : UR lo d len L m₀ t' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨(hk _ (by decide)).trans a1, (hk _ (by decide)).trans a2, (hk _ (by decide)).trans a3,
    (hk _ (by decide)).trans a4, (hk _ (by decide)).trans a5, (hk _ (by decide)).trans a6⟩

/-- `update`'s arguments, from its registers and the data's regions. -/
theorem eupdA {k : Nat} (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hb : BI w k L m₀ u)
    {lo d : BitVec 32} {len : Nat} (ha : UR lo d len L m₀ u) (hlen : len < 2 ^ 32)
    (hcd : Covers [⟨d.setWidth 64, len⟩] (u.rd ++ u.wr))
    (hdW : Region.Disjoint ⟨d.setWidth 64, len⟩ ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW).setWidth 64, w.F.H.S⟩)
    (hdS : Region.Disjoint ⟨d.setWidth 64, len⟩
      ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork).setWidth 64, w.ok.hH.Wb⟩)
    (hdC : L.CALLS.Disjoint ⟨d.setWidth 64, len⟩) (hnd : d.toNat + len ≤ 2 ^ 32) :
    UpdArgs w.ok.hH u .esi .edi (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) d
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork) lo len := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  have hx := hb.1
  obtain ⟨-, hS, -, hWb, -, -, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hbl : Region.Sub (Proof.Pbkdf2.Stream.X86.stk u) L.CALLS := sub_below hL hc (by decide)
  have hFN := hL.FN; have := hL.e0; have := hL.e1; have := hL.nB
  exact
    { hst := a1, hlo := a2, eax := a3, ecx := a5, edx := a4, ebp := a6, hr := by decide, hl := by decide
      hlen := hlen
      sp48 := by rw [hc.esp, hL.FN]; omega_arith
      cd := hcd
      cw := by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eW, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eWork, hL.frBase (by decide), by dsimp only; omega_arith⟩
      st_sc := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      d_st := hdW
      d_sc := hdS
      b_st := (hL.calls_fr (by omega_arith)).sub_left hbl
      b_d := hdC.sub_left hbl
      b_sc := (hL.calls_fr (by omega_arith)).sub_left hbl
      nst := by rw [hL.frN (by decide)]; omega_arith
      nd := hnd
      nsc := by rw [hL.frN (by decide)]; omega_arith }

/-- `update` through the table, on the working state: `len` bytes at `d` more. -/
theorem eupd_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t)
    {msg : List Byte → List Byte} {n : Nat} (hw : WS w L m₀ t.mem msg)
    (hn : ∀ prk, Keyd w L m₀ prk → (msg prk).length = n) {d : BitVec 32} {len : Nat}
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + n)) d len L m₀ t) (hBn : w.F.H.B + n < 2 ^ 32)
    (hA : ∀ u : State, Ctx ⟨w, f⟩ L g m₀ y u → BI w k L m₀ u → UR (BitVec.ofNat 32 (w.F.H.B + n)) d len L m₀ u →
      UpdArgs w.ok.hH u .esi .edi (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) d
        (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork) (BitVec.ofNat 32 (w.F.H.B + n)) len) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.eFr 5 1 f.upd Impl.Ecdsa.Rfc6979.X86.upd6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ BI w k L m₀ u ∧
        WS w L m₀ u.mem (fun prk => msg prk ++ Spec.Sha256.bytesAt t.mem (d.setWidth 64) len) := by
  refine tcall_ok (K := ⟨w, f⟩) hL hc (j := 1) (by decide) hc.tabMem.2.1 hc.tabOk.u fun t' c' hm' hk' _ => ?_
  have ua := hA t' c' (hb.mem hm') (ha.keep hk')
  have hx := hb.1
  obtain ⟨-, hS, -, hWb, -, -, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  refine WP.mono (upd_wp hL c' ua fun r hr => ?_) fun u ⟨cu, _, hf, hR⟩ => ⟨cu, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact .inr (.inl (hL.fr_hi (by decide) (by omega_arith)))
  · refine BI.keep (hb.mem hm') hf ?_ ?_ ?_ <;> intro r hr <;>
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl
    · exact vars_fr hL (by decide) (by omega_arith)
    · exact vars_fr hL (by decide) (by omega_arith)
    · exact vars_calls hL
    · exact (hL.fr_W (by omega_arith)).symm
    · exact (hL.fr_W (by omega_arith)).symm
    · exact hL.calls_W.symm
    · exact hL.fr_disj (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact (hL.calls_fr (by omega_arith)).symm
  · intro prk hk
    have h1 := hR _ (by rw [hm']; exact hw prk hk) (by
      rw [List.length_append, VG.Proof.Hmac.Common.xorPad_length, blockKey_length' (w := w), hn prk hk,
        Proof.Pbkdf2.Stream.X86.zero_append_ofNat hBn])
    rw [hm', List.append_assoc] at h1
    exact h1

theorem ofNat_add_bv (a : Nat) (x : BitVec 32) : BitVec.ofNat 32 a + x = BitVec.ofNat 32 (a + x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_add_mod]

/-- `update`'s arguments for `T(k)`. -/
theorem updT_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t) :
    WP isa (.block Impl.Hkdf.X86.updT) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧
      UR (BitVec.ofNat 32 (w.F.H.B + 0)) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT) (pl w k) L m₀ u ∧
      u.mem = t.mem := by
  rw [show Impl.Hkdf.X86.updT = Impl.Hkdf.X86.fr .edi Impl.Hkdf.X86.eW ++
      [.mov .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eB))] ++ [.mov .eax (.imm 0)] ++
      Impl.Hkdf.X86.fr .edx Impl.Hkdf.X86.eT ++ [.mov .ecx (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl))] ++
      Impl.Hkdf.X86.fr .ebp Impl.Hkdf.X86.eWork from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edi) (by decide) Impl.Hkdf.X86.eW) fun u₁ h₁ => ?_
  refine WP.mono (ldF_ok hL h₁.ctx (d := .esi) (by decide) (o := Impl.Hkdf.X86.eB) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (movi_ok hL h₂.ctx (d := .eax) (by decide) 0) fun u₃ h₃ => ?_
  refine WP.mono (fr_ok hL h₃.ctx (d := .edx) (by decide) Impl.Hkdf.X86.eT) fun u₄ h₄ => ?_
  refine WP.mono (ldF_ok hL h₄.ctx (d := .ecx) (by decide) (o := Impl.Hkdf.X86.eTl) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (fr_ok hL h₅.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.eWork) fun u₆ h₆ => ?_
  have hw := hb.2.2.1
  refine ⟨h₆.ctx, ⟨?_, ?_, ?_, ?_, ?_, h₆.val⟩, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val,
      h₁.mem, Nat.add_zero]; exact hw.b
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val, h₄.mem, h₃.mem, h₂.mem, h₁.mem]; exact hw.tl

/-- `update`'s arguments for `T(k)`, its regions. -/
theorem argsT {k : Nat} (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hb : BI w k L m₀ u)
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + 0)) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT) (pl w k) L m₀ u) :
    UpdArgs w.ok.hH u .esi .edi (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork) (BitVec.ofNat 32 (w.F.H.B + 0)) (pl w k) := by
  have hx := hb.1
  obtain ⟨-, hS, -, hWb, -, hD, -, hBB⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hpl := pl_le (w := w) k
  have hFN := hL.FN; have := hL.e0; have := hL.e1
  refine eupdA hL hc hb ha (by omega_arith) ?_ (hL.fr_disj (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (hL.calls_fr (by omega_arith))
    (by rw [hL.frN (by decide)]; omega_arith)
  refine VG.Covers.right ?_
  rw [hc.wr]
  refine VG.Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eT, hL.frBase (by decide), by dsimp only; omega_arith⟩

/-- `update` of `T(k)`. -/
theorem callT_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t)
    (hw : WS w L m₀ t.mem fun _ => [])
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + 0)) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT) (pl w k) L m₀ t) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.eFr 5 1 f.upd Impl.Ecdsa.Rfc6979.X86.upd6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ BI w k L m₀ u ∧
        WS w L m₀ u.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k := by
  have hx := hb.1
  obtain ⟨-, hS, -, hWb, -, hD, -, hBB⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hpl := pl_le (w := w) k
  have hFN := hL.FN; have := hL.e0; have := hL.e1
  refine WP.mono (eupd_ok hL hc hb hw (n := 0) (fun _ _ => rfl) ha (by omega_arith) fun u c b r => argsT hL c b r)
    fun u ⟨cu, bu, wu⟩ => ⟨cu, bu, wu.congr fun prk hk => ?_⟩
  rw [List.nil_append]; exact hb.2.2.2.2 prk hk

/-- `update`'s arguments for `info`. -/
theorem updI_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t) :
    WP isa (.block Impl.Hkdf.X86.updI) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧
      UR (BitVec.ofNat 32 (w.F.H.B + pl w k)) (L.a 1) (L.a 2).toNat L m₀ u ∧ u.mem = t.mem := by
  rw [show Impl.Hkdf.X86.updI = Impl.Hkdf.X86.fr .edi Impl.Hkdf.X86.eW ++
      [.mov .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eB))] ++
      [.alu .add .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl))] ++ [.mov .eax (.imm 0)] ++
      [.mov .edx (Impl.Hkdf.X86.argM eSh.FB 1)] ++ [.mov .ecx (Impl.Hkdf.X86.argM eSh.FB 2)] ++
      Impl.Hkdf.X86.fr .ebp Impl.Hkdf.X86.eWork from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edi) (by decide) Impl.Hkdf.X86.eW) fun u₁ h₁ => ?_
  refine WP.mono (ldF_ok hL h₁.ctx (d := .esi) (by decide) (o := Impl.Hkdf.X86.eB) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (addF_ok hL h₂.ctx (d := .esi) (by decide) (o := Impl.Hkdf.X86.eTl) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (movi_ok hL h₃.ctx (d := .eax) (by decide) 0) fun u₄ h₄ => ?_
  refine WP.mono (arg_ok hL h₄.ctx (d := .edx) (by decide) (i := 1) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (arg_ok hL h₅.ctx (d := .ecx) (by decide) (i := 2) (by decide)) fun u₆ h₆ => ?_
  refine WP.mono (fr_ok hL h₆.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.eWork) fun u₇ h₇ => ?_
  have hw := hb.2.2.1
  refine ⟨h₇.ctx, ⟨?_, ?_, ?_, ?_, ?_, h₇.val⟩, by rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]⟩
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide),
      h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val,
      h₂.val, h₂.mem, h₁.mem]
    show fw L Impl.Hkdf.X86.eB t.mem + fw L Impl.Hkdf.X86.eTl t.mem = _
    rw [hw.b, hw.tl, BitVec.ofNat_add_ofNat]
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.val]
  · rw [h₇.keep _ (by decide), h₆.val, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `update`'s arguments for `info`, its regions. -/
theorem argsI {k : Nat} (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hb : BI w k L m₀ u)
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + pl w k)) (L.a 1) (L.a 2).toNat L m₀ u) :
    UpdArgs w.ok.hH u .esi .edi (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) (L.a 1)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork) (BitVec.ofNat 32 (w.F.H.B + pl w k)) (L.a 2).toNat := by
  have hx := hb.1
  obtain ⟨-, hS, -, hWb, -, -, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  refine eupdA hL hc hb ha (L.a 2).isLt (VG.Covers.left ?_) (hx.kI.sub_left (hL.fr_sub (by omega_arith))).symm
    (hx.kI.sub_left (hL.fr_sub (by omega_arith))).symm (hx.kI.sub_left Lay.Ok.calls_stk) hx.ni
  rw [hc.rd]; exact VG.Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hx.iRd

/-- `update` of `info`. -/
theorem callI_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t)
    (hw : WS w L m₀ t.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k)
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + pl w k)) (L.a 1) (L.a 2).toNat L m₀ t) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.eFr 5 1 f.upd Impl.Ecdsa.Rfc6979.X86.upd6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ BI w k L m₀ u ∧
        WS w L m₀ u.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ := by
  have hx := hb.1
  have hpl := pl_le (w := w) k
  have hi := info_lt hL hx
  refine WP.mono (eupd_ok hL hc hb hw (n := pl w k) (fun prk _ => tBlock_len _ _ _) ha (by omega_arith)
    fun u c b r => argsI hL c b r) fun u ⟨cu, bu, wu⟩ => ⟨cu, bu, wu.congr fun prk _ => ?_⟩
  rw [hc.readBytes hx.iW hx.kI (L.a 2).isLt]

/-- The counter's byte stored, and `update`'s arguments for it. -/
theorem updC_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t)
    {msg : List Byte → List Byte} (hw : WS w L m₀ t.mem msg) :
    WP isa (.block Impl.Hkdf.X86.updC) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧
      UR (BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat))) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC) 1 L m₀ u ∧
      BI w k L m₀ u ∧ WS w L m₀ u.mem msg ∧
      Spec.Sha256.bytesAt u.mem ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC).setWidth 64) 1 = [BitVec.ofNat 8 (k + 1)] := by
  rw [show Impl.Hkdf.X86.updC = [.mov .eax (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eCnt))] ++
      [.store8 (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eC) .al] ++ Impl.Hkdf.X86.fr .edi Impl.Hkdf.X86.eW ++
      [.mov .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eB))] ++
      [.alu .add .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl))] ++
      [.alu .add .esi (Impl.Hkdf.X86.argM eSh.FB 2)] ++ [.mov .eax (.imm 0)] ++
      Impl.Hkdf.X86.fr .edx Impl.Hkdf.X86.eC ++ [.mov .ecx (.imm 1)] ++
      Impl.Hkdf.X86.fr .ebp Impl.Hkdf.X86.eWork from rfl]
  repeat rw [WP.block_append_iff]
  have hx := hb.1
  obtain ⟨-, hS, -, -, -, hD, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  refine WP.mono (ldF_ok hL hc (d := .eax) (by decide) (o := Impl.Hkdf.X86.eCnt) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (st8F_ok hL h₁.ctx .al (o := Impl.Hkdf.X86.eC) (by decide) (by decide))
    fun u₂ ⟨c₂, m₂, g₂, _⟩ => ?_
  refine WP.mono (fr_ok hL c₂ (d := .edi) (by decide) Impl.Hkdf.X86.eW) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .esi) (by decide) (o := Impl.Hkdf.X86.eB) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (addF_ok hL h₄.ctx (d := .esi) (by decide) (o := Impl.Hkdf.X86.eTl) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (addA_ok hL h₅.ctx (d := .esi) (by decide) (i := 2) (by decide)) fun u₆ h₆ => ?_
  refine WP.mono (movi_ok hL h₆.ctx (d := .eax) (by decide) 0) fun u₇ h₇ => ?_
  refine WP.mono (fr_ok hL h₇.ctx (d := .edx) (by decide) Impl.Hkdf.X86.eC) fun u₈ h₈ => ?_
  refine WP.mono (movi_ok hL h₈.ctx (d := .ecx) (by decide) 1) fun u₉ h₉ => ?_
  refine WP.mono (fr_ok hL h₉.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.eWork) fun u h => ?_
  have hm₂ : u.mem = u₂.mem := by rw [h.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem]
  have hbyte : (u₁.gpr Reg8.al.reg).setWidth 8 = BitVec.ofNat 8 (k + 1) := by
    rw [show Reg8.al.reg = .eax from rfl, h₁.val, show t.mem.readW _ 32 = fw L Impl.Hkdf.X86.eCnt t.mem from rfl,
      hb.2.2.1.cnt]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  have hm : u.mem = t.mem.writeW ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC).setWidth 64) (BitVec.ofNat 8 (k + 1)) := by
    rw [hm₂, m₂, hbyte, h₁.mem, hL.frv (by decide)]
  have hfr : Frame [⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC).setWidth 64, 1⟩] t.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hw' := hb.2.2.1
  refine ⟨h.ctx, ⟨?_, ?_, ?_, ?_, ?_, h.val⟩, ?_, ?_, ?_⟩
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide),
      h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide), h₆.val,
      h₅.val, h₄.val, h₄.mem, h₃.mem]
    show fw L Impl.Hkdf.X86.eB u₂.mem + fw L Impl.Hkdf.X86.eTl u₂.mem + L.a 2 = _
    rw [m₂, fw_write8 hL _ (by decide) (by decide) (by decide), fw_write8 hL _ (by decide) (by decide) (by decide),
      h₁.mem, hw'.b, hw'.tl, BitVec.ofNat_add_ofNat, ofNat_add_bv, Nat.add_assoc]
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.val]
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.val]
  · rw [h.keep _ (by decide), h₉.val]; rfl
  · refine hb.keep hfr ?_ ?_ ?_ <;> intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
    · exact vars_fr hL (by decide) (by decide)
    · exact (hL.fr_W (by decide)).symm
    · exact hL.fr_disj (.inl (by decide)) (by decide) (by decide)
  · intro prk hk
    refine w.ok.hH.repr t.mem u.mem _ _ _ (fun i hi => ?_) (hw prk hk)
    refine hfr.bytes (R := ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW).setWidth 64, w.F.H.S⟩) (fun r hr => ?_)
      (by dsimp only; omega_arith) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by decide)
  · rw [hm]
    simp only [Spec.Sha256.bytesAt, List.range_one, List.map_cons, List.map_nil, VG.WriteBytes.writeW8_apply,
      BitVec.add_zero, ite_true]

/-- `update`'s arguments for the counter's byte, its region. -/
theorem argsC {k : Nat} (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hb : BI w k L m₀ u)
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat))) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC) 1
      L m₀ u) :
    UpdArgs w.ok.hH u .esi .edi (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork) (BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat))) 1 := by
  have hx := hb.1
  obtain ⟨-, hS, -, hWb, -, -, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hFN := hL.FN; have := hL.e0; have := hL.e1
  refine eupdA hL hc hb ha (by decide) ?_ (hL.fr_disj (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (hL.calls_fr (by omega_arith))
    (by rw [hL.frN (by decide)]; omega_arith)
  refine VG.Covers.right ?_
  rw [hc.wr]
  refine VG.Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eC, hL.frBase (by decide), by dsimp only; omega_arith⟩

/-- `update` of the counter's byte. -/
theorem callC_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t)
    (hw : WS w L m₀ t.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀)
    (ha : UR (BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat))) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC) 1
      L m₀ t)
    (hcb : Spec.Sha256.bytesAt t.mem ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC).setWidth 64) 1 =
      [BitVec.ofNat 8 (k + 1)]) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.eFr 5 1 f.upd Impl.Ecdsa.Rfc6979.X86.upd6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ BI w k L m₀ u ∧
        WS w L m₀ u.mem fun prk =>
          Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ ++ [BitVec.ofNat 8 (k + 1)] := by
  have hx := hb.1
  have hpl := pl_le (w := w) k
  have hi := info_lt hL hx
  refine WP.mono (eupd_ok hL hc hb hw (n := pl w k + (L.a 2).toNat)
    (fun prk _ => by rw [List.length_append, tBlock_len, VG.Proof.Hmac.Common.bytesAt_length]) ha
    (by omega_arith) fun u c b r => argsC hL c b r)
    fun u ⟨cu, bu, wu⟩ => ⟨cu, bu, wu.congr fun prk _ => by rw [hcb]⟩

/-! ## A block: `finalize` -/

/-- `finalize`'s registers. -/
def FA (w : HVar) (k : Nat) : Pr eSh := fun L _ u =>
  u.gpr .edx = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW ∧ u.gpr .esi = L.a 0 + BitVec.ofNat 32 192 ∧
    u.gpr .eax = BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat + 1)) ∧ u.gpr .ecx = 0 ∧
    u.gpr .edi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT ∧ u.gpr .ebp = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork

theorem finT_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t) :
    WP isa (.block Impl.Hkdf.X86.finT) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ FA w k L m₀ u ∧ u.mem = t.mem := by
  rw [show Impl.Hkdf.X86.finT = Impl.Hkdf.X86.fr .edx Impl.Hkdf.X86.eW ++
      [.mov .esi (Impl.Hkdf.X86.argM eSh.FB 0)] ++ [.alu .add .esi (.imm 192)] ++
      [.mov .eax (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eB))] ++
      [.alu .add .eax (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl))] ++
      [.alu .add .eax (Impl.Hkdf.X86.argM eSh.FB 2)] ++ [.alu .add .eax (.imm 1)] ++ [.mov .ecx (.imm 0)] ++
      Impl.Hkdf.X86.fr .edi Impl.Hkdf.X86.eT ++ Impl.Hkdf.X86.fr .ebp Impl.Hkdf.X86.eWork from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edx) (by decide) Impl.Hkdf.X86.eW) fun u₁ h₁ => ?_
  refine WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 0) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (addI_ok hL h₂.ctx (d := .esi) (by decide) 192) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .eax) (by decide) (o := Impl.Hkdf.X86.eB) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (addF_ok hL h₄.ctx (d := .eax) (by decide) (o := Impl.Hkdf.X86.eTl) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (addA_ok hL h₅.ctx (d := .eax) (by decide) (i := 2) (by decide)) fun u₆ h₆ => ?_
  refine WP.mono (addI_ok hL h₆.ctx (d := .eax) (by decide) 1) fun u₇ h₇ => ?_
  refine WP.mono (movi_ok hL h₇.ctx (d := .ecx) (by decide) 0) fun u₈ h₈ => ?_
  refine WP.mono (fr_ok hL h₈.ctx (d := .edi) (by decide) Impl.Hkdf.X86.eT) fun u₉ h₉ => ?_
  refine WP.mono (fr_ok hL h₉.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.eWork) fun u h => ?_
  have hw := hb.2.2.1
  refine ⟨h.ctx, ⟨?_, ?_, ?_, ?_, ?_, h.val⟩,
    by rw [h.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]⟩
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide),
      h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.keep _ (by decide),
      h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val, h₂.val]; rfl
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.keep _ (by decide), h₇.val, h₆.val, h₅.val, h₄.val,
      h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    show fw L Impl.Hkdf.X86.eB t.mem + fw L Impl.Hkdf.X86.eTl t.mem + L.a 2 + BitVec.ofNat 32 1 = _
    rw [hw.b, hw.tl, BitVec.ofNat_add_ofNat, ofNat_add_bv, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat 32) (by omega)
  · rw [h.keep _ (by decide), h₉.keep _ (by decide), h₈.val]
  · rw [h.keep _ (by decide), h₉.val]

/-- `finalize`'s regions. -/
theorem finE {k : Nat} (hL : L.Ok) (hx : EOk w L) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (ha : FA w k L m₀ u) :
    HfArgs w.ok.hH.SH w.ok.Wf u (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eW) (L.a 0 + BitVec.ofNat 32 192)
      (BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat + 1))) 0 (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eWork) := by
  obtain ⟨hdx, hsi, hax, hcx, hdi, hbp⟩ := ha
  obtain ⟨hS, -, hWf, -, hD, hD64, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hb : Region.Sub (Proof.Pbkdf2.Whole.X86.stk u) L.CALLS := sub_below hL hc (by decide)
  have hFN := hL.FN; have := hL.e0; have := hL.e1; have nk := hx.nk
  have hk2 : (L.a 0 + BitVec.ofNat 32 192).setWidth 64 = (L.a 0).setWidth 64 + BitVec.ofNat 64 192 :=
    addr_eq (by omega_arith)
  have oK : Region.Sub ⟨(L.a 0 + BitVec.ofNat 32 192).setWidth 64, w.ok.hH.SH.stateBytes⟩
      ⟨(L.a 0).setWidth 64, 384⟩ := by
    rw [hk2]; exact Offset.sub_base _ (by omega_arith)
  exact
    { edx := hdx, esi := hsi, eax := hax, ecx := hcx, edi := hdi, ebp := hbp
      sp := by rw [hc.esp, hL.FN]; omega_arith
      cr := VG.Covers.left (by
        rw [hc.rd]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, hx.kRd, 192, hk2, by dsimp only; omega_arith⟩)
      cw := by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eW, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eT, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.eWork, hL.frBase (by decide), by dsimp only; omega_arith⟩
      i_u := (hx.kK.sub_left (hL.fr_sub (by omega_arith))).sub_right oK
      i_o := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      i_s := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      u_o := ((hx.kK.sub_left (hL.fr_sub (by omega_arith))).sub_right oK).symm
      u_s := ((hx.kK.sub_left (hL.fr_sub (by omega_arith))).sub_right oK).symm
      o_s := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      b_i := (hL.calls_fr (by omega_arith)).sub_left hb
      b_u := ((hx.kK.sub_left Lay.Ok.calls_stk).sub_right oK).sub_left hb
      b_o := (hL.calls_fr (by omega_arith)).sub_left hb
      b_s := (hL.calls_fr (by omega_arith)).sub_left hb
      ni := by rw [hL.frN (by decide)]; omega_arith
      nu := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 192) (by omega_arith),
          Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      no := by rw [hL.frN (by decide)]; omega_arith
      nsc := by rw [hL.frN (by decide)]; omega_arith }

/-- After `finalize`: our variables, `out`'s first bytes, and `T(k + 1)`. -/
def BF (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u =>
  EOk w L ∧ k * w.F.H.D < olen L ∧ Words w k L u.mem ∧ OB w k L m₀ u.mem ∧ TB w (k + 1) L m₀ u.mem

/-- `finalize` through the table: `T(k + 1)`. -/
theorem callF_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BI w k L m₀ t)
    (hw : WS w L m₀ t.mem fun prk =>
      Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ ++ [BitVec.ofNat 8 (k + 1)])
    (ha : FA w k L m₀ t) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.eFr 5 2 f.fin Impl.Ecdsa.Rfc6979.X86.fin6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ BF w k L m₀ u := by
  refine tcall_ok (K := ⟨w, f⟩) hL hc (j := 2) (by decide) hc.tabMem.2.2 hc.tabOk.f fun t' c' hm' hk' _ => ?_
  have ha' : FA w k L m₀ t' := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
    exact ⟨(hk' _ (by decide)).trans a1, (hk' _ (by decide)).trans a2, (hk' _ (by decide)).trans a3,
      (hk' _ (by decide)).trans a4, (hk' _ (by decide)).trans a5, (hk' _ (by decide)).trans a6⟩
  obtain ⟨hx, hlt, hwd, hob, -⟩ := hb
  obtain ⟨hS, hS', hWf, -, hD, hD64, -, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hpl := pl_le (w := w) k
  have hi := info_lt hL hx
  have hFN := hL.FN; have := hL.e0; have := hL.e1; have nk := hx.nk
  refine WP.mono (fin_wp hL c' (finE hL hx c' ha') fun r hr => ?_) fun u ⟨cu, _, hf, hpost⟩ =>
    ⟨cu, hx, hlt, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact .inr (.inl (hL.fr_hi (by decide) (by omega_arith)))
  · refine hwd.keep (hm' ▸ hf) fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact vars_fr hL (by decide) (by omega_arith)
    · exact vars_fr hL (by decide) (by omega_arith)
    · exact vars_fr hL (by decide) (by omega_arith)
    · exact vars_calls hL
  · intro prk hk
    rw [bytes_keep (hm' ▸ hf) (fun r hr => ?_)
      (Nat.le_trans (Nat.min_le_right _ _) (by show (L.a 4).toNat ≤ 2 ^ 64; have := (L.a 4).isLt; omega_arith))]
    · exact hob prk hk
    · have hs := out_sub0 hx (Nat.min_le_right (k * w.F.H.D) (olen L))
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hL.fr_W (by omega_arith)).symm.sub_left hs
      · exact (hL.fr_W (by omega_arith)).symm.sub_left hs
      · exact (hL.fr_W (by omega_arith)).symm.sub_left hs
      · exact hL.calls_W.symm.sub_left hs
  · intro prk hk
    have hB := w.ok.hH.hB
    have hk0 := blockKey_length' w prk
    have htl : (Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ ++
        [BitVec.ofNat 8 (k + 1)]).length = pl w k + (L.a 2).toNat + 1 := by
      rw [List.length_append, List.length_append, tBlock_len, VG.Proof.Hmac.Common.bytesAt_length,
        List.length_singleton]
    have hk2 : (L.a 0 + BitVec.ofNat 32 192).setWidth 64 = (L.a 0).setWidth 64 + BitVec.ofNat 64 192 :=
      addr_eq (by omega_arith)
    have e := hpost (Spec.Hmac.blockKey w.ok.hH.SH.H prk)
      (Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ ++ [BitVec.ofNat 8 (k + 1)]) (by rw [hk0, hB]) (by rw [hk0, htl]; omega_arith) (by rw [hm']; exact hw prk hk)
      (by rw [hB, htl]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by omega_arith))
      (by
        rw [hk2]
        refine w.ok.hH.repr m₀ t'.mem _ _ _ (fun i hi' => ?_) hk.2
        have hR : Region.Sub ⟨(L.a 0).setWidth 64 + BitVec.ofNat 64 192, 192⟩ ⟨(L.a 0).setWidth 64, 384⟩ :=
          Offset.sub_base _ (by decide)
        exact c'.bytes (R := ⟨(L.a 0).setWidth 64 + BitVec.ofNat 64 192, 192⟩) (hx.kW.sub_left hR)
          (hx.kK.symm.sub_left hR) (show 192 ≤ 2 ^ 64 by decide) (show i < 192 by omega_arith))
    rw [hD] at e
    rw [show pl w (k + 1) = w.F.H.D by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]]
    exact e

/-! ## A block: the output -/

/-- The bytes of `T(k + 1)` block `k + 1` copies to `out`. -/
abbrev nb (w : HVar) (L : Lay eSh) (k : Nat) : Nat := min w.F.H.D (olen L - k * w.F.H.D)

theorem BF.mem {k : Nat} {t t' : State} (h : BF w k L m₀ t) (hm : t'.mem = t.mem) : BF w k L m₀ t' := by
  unfold BF; rw [hm]; exact h

theorem done_lt {k : Nat} (h : k * w.F.H.D < olen L) : done w L k = k * w.F.H.D := Nat.min_eq_left (Nat.le_of_lt h)

theorem done_succ {k : Nat} (h : k * w.F.H.D < olen L) : done w L (k + 1) = k * w.F.H.D + nb w L k := by
  unfold done nb; rw [Nat.succ_mul]; omega

theorem ofNat_sub32 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The first `n` of `N` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n N : Nat} (h : n ≤ N) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p N).take n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (VG.Proof.Hmac.Common.bytesAt_length _ _ _)]

/-- `D` and `rem`, compared. -/
def OC (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u =>
  BF w k L m₀ u ∧ u.gpr .ecx = BitVec.ofNat 32 w.F.H.D ∧ u.gpr .edx = BitVec.ofNat 32 (olen L - k * w.F.H.D) ∧
    u.cf = some (decide (olen L - k * w.F.H.D < w.F.H.D))

/-- `min(D, rem)` in `ecx`. -/
def OL (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u => BF w k L m₀ u ∧ u.gpr .ecx = BitVec.ofNat 32 (nb w L k)

theorem outCmp_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BF w k L m₀ t) :
    WP isa (.block Impl.Hkdf.X86.outCmp) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ OC w k L m₀ u := by
  have hx := hb.1
  have hlt := hb.2.1
  have hwd := hb.2.2.1
  have hD := D_le hx
  have hol : olen L < 2 ^ 32 := (L.a 4).isLt
  rw [show Impl.Hkdf.X86.outCmp = [.mov .ecx (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eD))] ++
    [.mov .edx (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eRem))] ++ [.alu .cmp .edx (.reg .ecx)] from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc (d := .ecx) (by decide) (o := Impl.Hkdf.X86.eD) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (ldF_ok hL h₁.ctx (d := .edx) (by decide) (o := Impl.Hkdf.X86.eRem) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (cmp_ok hL h₂.ctx .edx .ecx) fun u₃ ⟨c₃, g₃, m₃, _, cf₃⟩ => ?_
  have hcx : u₂.gpr .ecx = BitVec.ofNat 32 w.F.H.D := by
    rw [h₂.keep _ (by decide), h₁.val]; exact hwd.d
  have hdx : u₂.gpr .edx = BitVec.ofNat 32 (olen L - k * w.F.H.D) := by
    rw [h₂.val, h₁.mem, ← done_lt hlt]; exact hwd.rem
  refine ⟨c₃, hb.mem (by rw [m₃, h₂.mem, h₁.mem]), by rw [g₃, hcx], by rw [g₃, hdx], ?_⟩
  rw [cf₃, hcx, hdx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem outB_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : OC w k L m₀ t)
    (hb : olen L - k * w.F.H.D < w.F.H.D) :
    WP isa (.block [.mov .ecx (.reg .edx)]) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ OL w k L m₀ u :=
  WP.mono (movr_ok hL hc (d := .ecx) (by decide) .edx) fun _ h' =>
    ⟨h'.ctx, h.1.mem h'.mem, by rw [h'.val, h.2.2.1]; exact congrArg (BitVec.ofNat 32) (by unfold nb; omega)⟩

theorem outE_ok {k : Nat} {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : OC w k L m₀ t)
    (hb : ¬ olen L - k * w.F.H.D < w.F.H.D) :
    WP isa (.block []) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ OL w k L m₀ u :=
  WP.block_nil ⟨hc, h.1, by rw [h.2.1]; exact congrArg (BitVec.ofNat 32) (by unfold nb; omega)⟩

/-- `min(D, rem)` into `ecx`. -/
theorem outLen_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BF w k L m₀ t) :
    WP isa Impl.Hkdf.X86.outLen t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ OL w k L m₀ u := by
  unfold Impl.Hkdf.X86.outLen
  refine WP.seq (WP.mono (outCmp_ok hL hc hb) fun u ⟨cu, hu⟩ => ?_)
  refine WP.ite (decide (olen L - k * w.F.H.D < w.F.H.D)) (by simp only [eval, hu.2.2.2]) (fun hb => ?_)
    (fun hb => ?_)
  · exact outB_ok hL cu hu (of_decide_eq_true hb)
  · exact outE_ok cu hu (of_decide_eq_false hb)

/-- The copy's arguments: `n` in `edi` too, `out`'s next byte, `T`. -/
theorem outA_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BF w k L m₀ t)
    (hcx : t.gpr .ecx = BitVec.ofNat 32 (nb w L k)) :
    WP isa (.block Impl.Hkdf.X86.outA) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ u.mem = t.mem ∧
      u.gpr .edi = BitVec.ofNat 32 (nb w L k) ∧ u.gpr .ebx = L.a 3 + BitVec.ofNat 32 (k * w.F.H.D) ∧
      u.gpr .esi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT ∧ u.gpr .ecx = BitVec.ofNat 32 (nb w L k) ∧
      (∀ r, r ≠ .edi → r ≠ .ebx → r ≠ .esi → u.gpr r = t.gpr r) := by
  rw [show Impl.Hkdf.X86.outA = [.mov .edi (.reg .ecx)] ++ [.mov .ebx (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eOut))] ++
    Impl.Hkdf.X86.fr .esi Impl.Hkdf.X86.eT from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (movr_ok hL hc (d := .edi) (by decide) .ecx) fun u₁ h₁ => ?_
  refine WP.mono (ldF_ok hL h₁.ctx (d := .ebx) (by decide) (o := Impl.Hkdf.X86.eOut) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .esi) (by decide) Impl.Hkdf.X86.eT) fun u h => ?_
  refine ⟨h.ctx, by rw [h.mem, h₂.mem, h₁.mem], ?_, ?_, h.val, ?_, fun r h1 h2 h3 => ?_⟩
  · rw [h.keep _ (by decide), h₂.keep _ (by decide), h₁.val, hcx]
  · rw [h.keep _ (by decide), h₂.val, h₁.mem, ← done_lt hb.2.1]; exact hb.2.2.1.outp
  · rw [h.keep _ (by decide), h₂.keep _ (by decide), h₁.keep _ (by decide), hcx]
  · rw [h.keep _ h3, h₂.keep _ h2, h₁.keep _ h1]

/-- After the copy to `out`: our variables, `out`'s first `done (k + 1)`
bytes, `T(k + 1)`, `n` in `edi`, and `out` past the bytes in `ebx`. -/
def NB (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u =>
  EOk w L ∧ k * w.F.H.D < olen L ∧ Words w k L u.mem ∧ OB w (k + 1) L m₀ u.mem ∧ TB w (k + 1) L m₀ u.mem ∧
    u.gpr .edi = BitVec.ofNat 32 (nb w L k) ∧ u.gpr .ebx = L.a 3 + BitVec.ofNat 32 (done w L (k + 1))

/-- The copy of `nb` bytes of `T(k + 1)` to `out`. -/
theorem outCp_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (hb : BF w k L m₀ t)
    (hdi : t.gpr .edi = BitVec.ofNat 32 (nb w L k)) (hbx : t.gpr .ebx = L.a 3 + BitVec.ofNat 32 (k * w.F.H.D))
    (hsi : t.gpr .esi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT) (hcx : t.gpr .ecx = BitVec.ofNat 32 (nb w L k)) :
    WP isa Impl.Hkdf.X86.cpLoop t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ NB w k L m₀ u := by
  obtain ⟨hx, hlt, hwd, hob, htb⟩ := hb
  obtain ⟨-, -, -, -, -, hD, hD0, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hol : olen L < 2 ^ 32 := (L.a 4).isLt
  have hol' : olen L = (L.a 4).toNat := rfl
  have hno := hx.no
  have hFN := hL.FN; have := hL.e0; have := hL.e1; have := hL.nB
  have hn0 : 0 < nb w L k := by unfold nb; omega
  have hnD : nb w L k ≤ w.F.H.D := Nat.min_le_left _ _
  have hnR : k * w.F.H.D + nb w L k ≤ olen L := by unfold nb; omega
  have hds := done_succ (w := w) hlt
  have hDv : (L.a 3 + BitVec.ofNat 32 (k * w.F.H.D)).setWidth 64 =
      (L.a 3).setWidth 64 + BitVec.ofNat 64 (k * w.F.H.D) := addr_eq (by omega_arith)
  have hDn : (L.a 3 + BitVec.ofNat 32 (k * w.F.H.D)).toNat = (L.a 3).toNat + k * w.F.H.D := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k * w.F.H.D) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  have hoS : Region.Sub ⟨(L.a 3).setWidth 64 + BitVec.ofNat 64 (k * w.F.H.D), nb w L k⟩ L.W := out_sub hx hnR
  refine WP.mono (cp_ok hL hc (Sv := L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT)
    (Dv := L.a 3 + BitVec.ofNat 32 (k * w.F.H.D)) (n := nb w L k) hn0 (by omega_arith)
    (by rw [hL.frN (by decide)]; omega_arith) (by rw [hDn]; omega_arith)
    ⟨L.FR, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self),
      by rw [hL.frBase (by decide)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    ⟨L.W, by rw [hc.wr]; exact List.mem_cons_of_mem _ hL.wWr,
      by rw [hDv, hx.W]; exact Offset.contains_base _ hnR (by omega_arith)⟩
    (by rw [hDv]; exact (hL.fr_W (by omega_arith)).sub_right hoS) (.inl (by rw [hDv]; exact hoS))
    hsi hbx hcx) fun t₂ ⟨c₂, hf₂, hbs₂, hk₂, hbx₂⟩ => ⟨c₂, hx, hlt, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hDv] at hf₂ hbs₂
  · exact hwd.keep hf₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (vars_W hL).sub_right hoS
  · intro prk hk
    have hbl := Proof.Hkdf.blocks_length w.ok.hH.SH.H prk (infoOf L m₀) w.hlen k
    have hT := htb prk hk
    rw [show pl w (k + 1) = w.F.H.D by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]] at hT
    show Spec.Sha256.bytesAt t₂.mem ((L.a 3).setWidth 64) (done w L (k + 1)) =
      (Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf L m₀) (k + 1) [] 1).take (done w L (k + 1))
    rw [hds, Proof.Hkdf.blocks_succ, List.take_append, List.take_of_length_le (by omega_arith), hbl,
      Nat.add_sub_cancel_left, VG.Proof.Hmac.Common.bytesAt_add, hbs₂, ← hT, ← bytesAt_take _ _ hnD]
    congr 1
    rw [bytes_keep hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)) (by omega_arith)]
    have := hob prk hk
    rw [done_lt hlt] at this
    rw [this, List.take_of_length_le (by omega_arith)]
  · intro prk hk
    have hT := htb prk hk
    have hpl : pl w (k + 1) = w.F.H.D := by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
    show Spec.Sha256.bytesAt t₂.mem ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT).setWidth 64) (pl w (k + 1)) = _
    rw [hpl] at hT ⊢
    rw [bytes_keep hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.fr_W (by omega_arith)).sub_right hoS) (by omega_arith)]
    exact hT
  · rw [hk₂ _ (by decide) (by decide) (by decide) (by decide), hdi]
  · rw [hbx₂, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hds]

/-- The variables for block `k + 2`: `EI (k + 1)`. -/
theorem nextB_ok {k : Nat} (hL : L.Ok) {t₂ : State} (c₂ : Ctx ⟨w, f⟩ L g m₀ y t₂) (hb : NB w k L m₀ t₂) :
    WP isa (.block Impl.Hkdf.X86.nextBlock) t₂ fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ EI w (k + 1) L m₀ u := by
  obtain ⟨hx, hlt, hw₂, hob, htb, hdi₂, vOut⟩ := hb
  obtain ⟨-, -, -, -, -, hD, hD0, -⟩ := esizes hx
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, e1, e2, e3, e4⟩ := econsts
  have hol : olen L < 2 ^ 32 := (L.a 4).isLt
  have hol' : olen L = (L.a 4).toNat := rfl
  have := hL.nB
  have hnR : k * w.F.H.D + nb w L k ≤ olen L := by unfold nb; omega
  have hds := done_succ (w := w) hlt
  rw [show Impl.Hkdf.X86.nextBlock = [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eOut) .ebx] ++
      [.mov .edx (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eRem))] ++ [.alu .sub .edx (.reg .edi)] ++
      [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eRem) .edx] ++ [.mov .ecx (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eD))] ++
      [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eTl) .ecx] ++ [.mov .eax (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eCnt))] ++
      [.alu .add .eax (.imm 1)] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.eCnt) .eax] ++
      [.alu .test .edx (.reg .edx)] from rfl]
  repeat rw [WP.block_append_iff]
  refine WP.mono (stF_ok hL c₂ .ebx (o := Impl.Hkdf.X86.eOut) (by decide) (by decide)) fun u₃ ⟨c₃, m₃, g₃, _⟩ => ?_
  refine WP.mono (ldF_ok hL c₃ (d := .edx) (by decide) (o := Impl.Hkdf.X86.eRem) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (subR_ok hL h₄.ctx (d := .edx) (by decide) .edi) fun u₅ h₅ => ?_
  refine WP.mono (stF_ok hL h₅.ctx .edx (o := Impl.Hkdf.X86.eRem) (by decide) (by decide)) fun u₆ ⟨c₆, m₆, g₆, _⟩ => ?_
  refine WP.mono (ldF_ok hL c₆ (d := .ecx) (by decide) (o := Impl.Hkdf.X86.eD) (by decide)) fun u₇ h₇ => ?_
  refine WP.mono (stF_ok hL h₇.ctx .ecx (o := Impl.Hkdf.X86.eTl) (by decide) (by decide)) fun u₈ ⟨c₈, m₈, g₈, _⟩ => ?_
  refine WP.mono (ldF_ok hL c₈ (d := .eax) (by decide) (o := Impl.Hkdf.X86.eCnt) (by decide)) fun u₉ h₉ => ?_
  refine WP.mono (addI_ok hL h₉.ctx (d := .eax) (by decide) 1) fun u₁₀ h₁₀ => ?_
  refine WP.mono (stF_ok hL h₁₀.ctx .eax (o := Impl.Hkdf.X86.eCnt) (by decide) (by decide))
    fun u₁₁ ⟨c₁₁, m₁₁, g₁₁, _⟩ => ?_
  refine WP.mono (test_ok hL c₁₁ .edx) fun u ⟨cu, gu, mu, _, zu⟩ => ⟨cu, hx, ?_, ?_, ?_, ?_⟩
  all_goals
    have vRem : u₅.gpr .edx = BitVec.ofNat 32 (olen L - done w L (k + 1)) := by
      rw [h₅.val, h₄.val, h₄.keep _ (by decide), g₃, hdi₂, m₃]
      show fw L Impl.Hkdf.X86.eRem (t₂.mem.writeW _ _) - _ = _
      rw [fw_write hL _ (by decide) (by decide) (by decide), hw₂.rem, done_lt hlt, hds,
        ofNat_sub32 (by omega) (by omega)]
      exact congrArg (BitVec.ofNat 32) (by omega)
    have vTl : u₇.gpr .ecx = BitVec.ofNat 32 w.F.H.D := by
      rw [h₇.val, m₆, h₅.mem, h₄.mem, m₃]
      show fw L Impl.Hkdf.X86.eD ((t₂.mem.writeW _ _).writeW _ _) = _
      rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide)]
      exact hw₂.d
    have vCnt : u₁₀.gpr .eax = BitVec.ofNat 32 (k + 1 + 1) := by
      rw [h₁₀.val, h₉.val, m₈, h₇.mem, m₆, h₅.mem, h₄.mem, m₃]
      show fw L Impl.Hkdf.X86.eCnt (((t₂.mem.writeW _ _).writeW _ _).writeW _ _) + BitVec.ofNat 32 1 = _
      rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide), hw₂.cnt, BitVec.ofNat_add_ofNat]
    have hM : u.mem = (((t₂.mem.writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eOut))
        (L.a 3 + BitVec.ofNat 32 (done w L (k + 1)))).writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eRem))
        (BitVec.ofNat 32 (olen L - done w L (k + 1)))).writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eTl))
        (BitVec.ofNat 32 w.F.H.D)).writeW (L.B + BitVec.ofNat 64 (eSh.cb + Impl.Hkdf.X86.eCnt))
        (BitVec.ofNat 32 (k + 1 + 1)) := by
      rw [mu, m₁₁, vCnt, h₁₀.mem, h₉.mem, m₈, vTl, h₇.mem, m₆, vRem, h₅.mem, h₄.mem, m₃, vOut]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hM]
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide)]
      exact hw₂.d
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide)]
      exact hw₂.b
    · exact fw_self _
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide)]
      exact fw_self _
    · rw [fw_write hL _ (by decide) (by decide) (by decide), fw_write hL _ (by decide) (by decide) (by decide),
        fw_write hL _ (by decide) (by decide) (by decide)]
      exact fw_self _
    · rw [fw_write hL _ (by decide) (by decide) (by decide)]
      rw [fw_self]; simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
  all_goals
    have hvr : ∀ o, 16 ≤ o → o + 4 ≤ 40 → (⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩ : Region).Contains
        (L.B + BitVec.ofNat 64 (eSh.cb + o)) 4 := fun o h₁ h₂ =>
      Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    have hF : Frame [⟨L.B + BitVec.ofNat 64 (eSh.cb + 16), 24⟩] t₂.mem u.mem := by
      rw [hM]
      exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (hvr _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (hvr _ (by decide) (by decide))).writeW List.mem_cons_self _
        (hvr _ (by decide) (by decide))).writeW List.mem_cons_self _ (hvr _ (by decide) (by decide))
  · intro prk hk
    rw [bytes_keep hF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((vars_W hL).sub_right (out_sub0 hx (Nat.min_le_right _ _))).symm)
      (Nat.le_trans (Nat.min_le_right _ _) (by omega_arith))]
    exact hob prk hk
  · intro prk hk
    rw [bytes_keep hF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (vars_fr hL (by decide) (by
          have := pl_le (w := w) (k + 1); omega_arith)).symm) (by have := pl_le (w := w) (k + 1); omega_arith)]
    exact htb prk hk
  · rw [zu, g₁₁, h₁₀.keep _ (by decide), h₉.keep _ (by decide), g₈, h₇.keep _ (by decide), g₆, vRem]

/-! ## The blocks -/

/-- While bytes of `out` are left, before block `k + 1` is during it. -/
theorem ei_bi {k : Nat} {t : State} (h : EI w k L m₀ t) (hs : olen L - done w L k ≠ 0) : BI w k L m₀ t := by
  obtain ⟨hx, hw, hob, htb, -⟩ := h
  have hlt : k * w.F.H.D < olen L := by
    refine Nat.lt_of_not_le fun hc => hs ?_
    rw [show done w L k = olen L from Nat.min_eq_right hc, Nat.sub_self]
  exact ⟨hx, hlt, hw, hob, htb⟩

/-- One block. -/
theorem block_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : EI w k L m₀ t)
    (hs : olen L - done w L k ≠ 0) :
    WP isa (Impl.Hkdf.X86.block f) t fun u => Ctx ⟨w, f⟩ L g m₀ y u ∧ EI w (k + 1) L m₀ u := by
  have hb := ei_bi h hs
  unfold Impl.Hkdf.X86.block
  refine WP.seq (WP.mono (copyA_ok hL hc hb) fun t₁ ⟨c₁, a₁⟩ => ?_)
  refine WP.seq (WP.mono (copyW_ok hL c₁ a₁) fun t₂ ⟨c₂, b₂, w₂⟩ => ?_)
  refine WP.seq (WP.mono (updT_ok hL c₂ b₂) fun t₃ ⟨c₃, r₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (callT_ok hL c₃ (b₂.mem m₃) (by rw [m₃]; exact w₂) r₃) fun t₄ ⟨c₄, b₄, w₄⟩ => ?_)
  refine WP.seq (WP.mono (updI_ok hL c₄ b₄) fun t₅ ⟨c₅, r₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (callI_ok hL c₅ (b₄.mem m₅) (by rw [m₅]; exact w₄) r₅) fun t₆ ⟨c₆, b₆, w₆⟩ => ?_)
  refine WP.seq (WP.mono (updC_ok hL c₆ b₆ w₆) fun t₇ ⟨c₇, r₇, b₇, w₇, y₇⟩ => ?_)
  refine WP.seq (WP.mono (callC_ok hL c₇ b₇ w₇ r₇ y₇) fun t₈ ⟨c₈, b₈, w₈⟩ => ?_)
  refine WP.seq (WP.mono (finT_ok hL c₈ b₈) fun t₉ ⟨c₉, a₉, m₉⟩ => ?_)
  refine WP.seq (WP.mono (callF_ok hL c₉ (b₈.mem m₉) (by rw [m₉]; exact w₈) a₉) fun t₁₀ ⟨c₁₀, f₁₀⟩ => ?_)
  refine WP.seq (WP.mono (outLen_ok hL c₁₀ f₁₀) fun t₁₁ ⟨c₁₁, f₁₁, x₁₁⟩ => ?_)
  refine WP.seq (WP.mono (outA_ok hL c₁₁ f₁₁ x₁₁) fun t₁₂ ⟨c₁₂, m₁₂, d₁₂, b₁₂, s₁₂, x₁₂, _⟩ => ?_)
  exact WP.seq (WP.mono (outCp_ok hL c₁₂ (f₁₁.mem m₁₂) d₁₂ b₁₂ s₁₂ x₁₂) fun t₁₃ ⟨c₁₃, n₁₃⟩ =>
    nextB_ok hL c₁₃ n₁₃)

theorem ofNat_beq_zero32 {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
  · intro e; rw [e]; rfl

/-- Whether bytes of `out` are left, as the loop's condition reads it. -/
theorem eval_ne {k : Nat} {t : State} (h : EI w k L m₀ t) :
    eval .ne t = some (decide (olen L - done w L k ≠ 0)) := by
  have hol : olen L < 2 ^ 32 := (L.a 4).isLt
  simp only [eval, h.2.2.2.2, Option.map_some]
  congr 1
  rw [ofNat_beq_zero32 (by omega)]
  simp only [decide_not]

/-- The blocks, while bytes of `out` are left. -/
theorem loop_ok {k : Nat} (hL : L.Ok) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (h : EI w k L m₀ t)
    (hs : olen L - done w L k ≠ 0) :
    WP isa (.loop (Impl.Hkdf.X86.block f) .ne) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ ∃ K, EI w K L m₀ u ∧ olen L ≤ K * w.F.H.D := by
  have hD0 : 0 < w.F.H.D := (esizes h.1).2.2.2.2.2.2.1
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = olen L - j * w.F.H.D ∧ Ctx ⟨w, f⟩ L g m₀ y u ∧
    EI w j L m₀ u ∧ olen L - done w L j ≠ 0) ?_ _ t ⟨k, rfl, hc, h, hs⟩
  rintro n u ⟨j, rfl, cj, hj, hu⟩
  have hlt := (ei_bi hj hu).2.1
  refine WP.mono (block_ok hL cj hj hu) fun v ⟨cv, hv⟩ => ?_
  rw [show isa.eval .ne v = _ from eval_ne hv]
  by_cases e : olen L ≤ (j + 1) * w.F.H.D
  · refine .inl ⟨?_, cv, j + 1, hv, e⟩
    rw [show done w L (j + 1) = olen L from Nat.min_eq_right e, Nat.sub_self]; rfl
  · have hd : done w L (j + 1) = (j + 1) * w.F.H.D := Nat.min_eq_left (by omega)
    have hsm : (j + 1) * w.F.H.D = j * w.F.H.D + w.F.H.D := Nat.succ_mul _ _
    refine .inr ⟨?_, olen L - (j + 1) * w.F.H.D, by omega, j + 1, rfl, cv, hv, ?_⟩
    · rw [hd, decide_eq_true (by omega : olen L - (j + 1) * w.F.H.D ≠ 0)]
    · rw [hd]; omega

/-- The frame's body of `vg_hkdf_expand`. -/
theorem expandBody_ok {s : State} (hL : (layE w s).Ok) (hx : EOk w (layE w s)) (he : Entry ⟨w, f⟩ (layE w s) s) :
    WP isa (Impl.Hkdf.X86.expandBody f) (allocFrame eSh.FB s) fun u =>
      Ctx ⟨w, f⟩ (layE w s) s.gpr s.mem s.syms u ∧ (∀ p ∈ Impl.Hkdf.X86.saved, u.gpr p.1 = s.gpr p.1) ∧
      ∀ prk, Keyd w (layE w s) s.mem prk →
        Spec.Sha256.bytesAt u.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
          (Spec.Hkdf.blocks w.ok.hH.SH.H prk (infoOf (layE w s) s.mem)
            (((arg s 4).toNat + w.F.H.D - 1) / w.F.H.D) [] 1).take (arg s 4).toNat := by
  have hD0 : 0 < w.F.H.D := (esizes hx).2.2.2.2.2.2.1
  have a3 := layE_a (w := w) (s := s) (i := 3) (by decide)
  have a4 := layE_a (w := w) (s := s) (i := 4) (by decide)
  unfold Impl.Hkdf.X86.expandBody
  refine WP.seq (WP.mono (entry_ok hL he) fun t₁ ⟨c₁, ax⟩ => ?_)
  refine WP.seq (WP.mono (etab_ok hL c₁ ⟨hx, ax⟩) fun t₂ ⟨c₂, h₂⟩ => ?_)
  have hd0 : done w (layE w s) 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  refine WP.seq (WP.mono (Q := fun (u : State) => Ctx ⟨w, f⟩ (layE w s) s.gpr s.mem s.syms u ∧
      ∃ K, EI w K (layE w s) s.mem u ∧ olen (layE w s) ≤ K * w.F.H.D)
    (WP.ite _ (eval_ne h₂) (fun ht => ?_) (fun hf => ?_)) fun t₃ ⟨c₃, K, h₃, hK⟩ => ?_)
  · exact loop_ok hL c₂ h₂ (of_decide_eq_true ht)
  · refine WP.block_nil ⟨c₂, 0, h₂, ?_⟩
    have := of_decide_eq_false hf
    rw [hd0, Nat.sub_zero] at this
    rw [Decidable.not_not.mp this]; exact Nat.zero_le _
  refine WP.mono (restore_ok hL c₃) fun u ⟨cu, hr, hm⟩ => ⟨cu, hr, fun prk hk => ?_⟩
  have hdK : done w (layE w s) K = olen (layE w s) := Nat.min_eq_right hK
  have ob := h₃.2.2.1 prk hk
  have ho : olen (layE w s) = (arg s 4).toNat := by show ((layE w s).a 4).toNat = _; rw [a4]
  rw [hdK] at ob
  rw [a3, ho] at ob
  rw [hm, ob]
  have hN : (arg s 4).toNat ≤ ((arg s 4).toNat + w.F.H.D - 1) / w.F.H.D * w.F.H.D := by
    have e₁ := Nat.div_add_mod ((arg s 4).toNat + w.F.H.D - 1) w.F.H.D
    have e₂ := Nat.mod_lt ((arg s 4).toNat + w.F.H.D - 1) hD0
    rw [Nat.mul_comm] at e₁
    omega
  rw [ho] at hK
  have tk := fun a b (ha : (arg s 4).toNat ≤ a * w.F.H.D) =>
    Proof.Hkdf.blocks_take w.ok.hH.SH.H prk (infoOf (layE w s) s.mem) w.hlen (a := a) ha b
  rcases Nat.le_total K (((arg s 4).toNat + w.F.H.D - 1) / w.F.H.D) with hl | hl
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
    rw [hj, tk K j hK]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
    rw [hj, tk _ j hN]

/-- `vg_hkdf_expand`: its frame, `D` and `B`, and for each block HMAC's
`update` and `finalize` through the table. -/
theorem expand_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hsp : NoSp (Impl.Hkdf.X86.expandBody f)) (hp : (expandR w f ns eStack).pre s) :
    WP isa (Impl.Hkdf.X86.expand f) s fun s' => abiPreserved s s' ∧ (expandR w f ns eStack).post s s' := by
  obtain ⟨hL, hx⟩ := layE_ok hw hp
  have he := entryE hp
  have ol : (arg s 4).toNat ≤ 255 * w.F.H.D := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine WP.mono (frame_ok hL he hsp (expandBody_ok hL hx he)) fun s' ⟨ha, u, hu, hm⟩ => ⟨ha, fun prk hk => ?_⟩
  have a0 := layE_a (w := w) (s := s) (i := 0) (by decide)
  have a1 := layE_a (w := w) (s := s) (i := 1) (by decide)
  have a2 := layE_a (w := w) (s := s) (i := 2) (by decide)
  have hk' : Keyd w (layE w s) s.mem prk := by show Spec.Hkdf.Keyed _ _ _ _; rw [a0]; exact hk
  have e := hu prk hk'
  have hW := hx.W
  rw [layE_a (by decide), layE_a (by decide)] at hW
  have e' : Spec.Sha256.bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha256.bytesAt u.mem ((arg s 3).setWidth 64) (arg s 4).toNat := by
    simp only [Spec.Sha256.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact (hm.bytes (R := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [← hW]; exact (hL.kW.sub_left Lay.Ok.fr_stk).symm)
      (by have := (arg s 4).isLt; dsimp only; omega_arith) (List.mem_range.mp hi))
  rw [e', e]
  unfold Spec.Hkdf.expand
  rw [ite_eq_right (Nat.not_lt.mpr ol)]
  simp only [infoOf, a1, a2]

end

/-! ## Constant time -/

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The layouts of two calls whose public data agree. -/
theorem layE_eq (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) {N : Nat} {s₁ s₂ : State}
    (hpub : (expandR w f ns N).pub s₁ s₂) : layE w s₂ = layE w s₁ := by
  obtain ⟨hsp, ha, hsy⟩ := hpub
  have hfa : faOf w s₂ = faOf w s₁ := funext fun n => by
    unfold faOf; split
    · next h => exact (hsy n (hns n h)).symm
    · rfl
  have haf : (fun i => if i < 6 then arg s₂ i else 0) = fun i => if i < 6 then arg s₁ i else 0 := funext fun i => by
    split
    · next h => exact (ha i h).symm
    · rfl
  have hA : argAddr s₂ 0 = argAddr s₁ 0 := by simp only [argAddr, hsp]
  simp only [layE, hfa, haf, hA, hsp, ← ha 0 (by decide), ← ha 1 (by decide), ← ha 2 (by decide),
    ← ha 3 (by decide), ← ha 4 (by decide), ← ha 5 (by decide)]

theorem entry_taintE : TaintOk [.esp] (.block (Impl.Hkdf.X86.entry eSh.FB eSh.ti)) := ⟨_, by taint_decide⟩
theorem etab_taint : TaintOk [.esp, .eax] (.block Impl.Hkdf.X86.expandTab) := ⟨_, by taint_decide⟩
theorem copyA_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.copyA) := ⟨_, by taint_decide⟩
theorem updT_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.updT) := ⟨_, by taint_decide⟩
theorem updI_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.updI) := ⟨_, by taint_decide⟩
theorem updC_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.updC) := ⟨_, by taint_decide⟩
theorem finT_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.finT) := ⟨_, by taint_decide⟩
theorem outCmp_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.outCmp) := ⟨_, by taint_decide⟩
theorem movcx_taint : TaintOk [.esp] (.block [.mov .ecx (.reg .edx)]) := ⟨_, by taint_decide⟩
theorem nil_taint : TaintOk [.esp] (.block []) := ⟨_, by taint_decide⟩
theorem outA_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.outA) := ⟨_, by taint_decide⟩
theorem next_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.nextBlock) := ⟨_, by taint_decide⟩
theorem tblk1_taintE : TaintOk [.esp] (.block [.mov .ebx (Impl.Hkdf.X86.argM eSh.FB eSh.ti)]) :=
  ⟨_, by taint_decide⟩

/-- The copy's arguments, and the out copy's, agree. -/
theorem agreeCA {k : Nat} : Agree ⟨w, f⟩ (CA w k) [.esi, .ebx, .ecx] := by
  intro L t₁ t₂ _ _ _ _ _ _ _ _ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.2.1.trans f₂.2.1.symm
  · exact f₁.2.2.1.trans f₂.2.2.1.symm
  · exact f₁.2.2.2.trans f₂.2.2.2.symm

/-- The out copy's arguments. -/
def OA (w : HVar) (k : Nat) : Pr eSh := fun L m₀ u =>
  BF w k L m₀ u ∧ u.gpr .edi = BitVec.ofNat 32 (nb w L k) ∧ u.gpr .ebx = L.a 3 + BitVec.ofNat 32 (k * w.F.H.D) ∧
    u.gpr .esi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT ∧ u.gpr .ecx = BitVec.ofNat 32 (nb w L k)

theorem agreeOA {k : Nat} : Agree ⟨w, f⟩ (OA w k) [.esi, .ebx, .ecx] := by
  intro L t₁ t₂ _ _ _ _ _ _ _ _ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.2.2.2.1.trans f₂.2.2.2.1.symm
  · exact f₁.2.2.1.trans f₂.2.2.1.symm
  · exact f₁.2.2.2.2.trans f₂.2.2.2.2.symm

/-- `min(D, rem)` in two runs. -/
theorem outLen_rel {k : Nat} (e : Env2 eSh) :
    RelCT isa (TwoAt ⟨w, f⟩ (BF w k) e) Impl.Hkdf.X86.outLen (TwoAt ⟨w, f⟩ (OL w k) e) := by
  unfold Impl.Hkdf.X86.outLen
  refine (two_wpAt (Ψ := OC w k) (two_prog [.esp] espOnly outCmp_taint)
    fun L g m₀ y t hL hc hb => outCmp_ok hL hc hb).seq (RelCT.ite (fun s₁ s₂ ⟨_, _, _, f₁, f₂⟩ => by
      simp only [eval, f₁.2.2.2, f₂.2.2.2]) ?_ ?_)
  · refine (two_wpAt (Φ := fun L m₀ u => OC w k L m₀ u ∧ olen L - k * w.F.H.D < w.F.H.D)
      (two_prog [.esp] espOnly movcx_taint) fun L g m₀ y t hL hc ⟨h, hb⟩ => outB_ok hL hc h hb).mono
      (fun s₁ s₂ ⟨⟨hL, c₁, c₂, f₁, f₂⟩, hev⟩ => ?_) fun _ _ h => h
    have hb : olen e.L - k * w.F.H.D < w.F.H.D := by
      simp only [eval, f₁.2.2.2, Option.some.injEq, decide_eq_true_eq] at hev; exact hev
    exact ⟨hL, c₁, c₂, ⟨f₁, hb⟩, ⟨f₂, hb⟩⟩
  · refine (two_wpAt (Φ := fun L m₀ u => OC w k L m₀ u ∧ ¬ olen L - k * w.F.H.D < w.F.H.D)
      (two_prog [.esp] espOnly nil_taint) fun L g m₀ y t _ hc ⟨h, hb⟩ => outE_ok hc h hb).mono
      (fun s₁ s₂ ⟨⟨hL, c₁, c₂, f₁, f₂⟩, hev⟩ => ?_) fun _ _ h => h
    have hb : ¬ olen e.L - k * w.F.H.D < w.F.H.D := by
      simp only [eval, f₁.2.2.2, Option.some.injEq, decide_eq_false_iff_not] at hev; exact hev
    exact ⟨hL, c₁, c₂, ⟨f₁, hb⟩, ⟨f₂, hb⟩⟩

/-- Two runs of block `k + 1`, with the same layout. -/
theorem block_rel (k : Nat) (e : Env2 eSh) :
    RelCT isa (TwoAt ⟨w, f⟩ (BI w k) e) (Impl.Hkdf.X86.block f) (TwoAt ⟨w, f⟩ (EI w (k + 1)) e) := by
  unfold Impl.Hkdf.X86.block
  refine (two_wpAt (Ψ := CA w k) (two_prog [.esp] espOnly copyA_taint)
    fun L g m₀ y t hL hc hb => copyA_ok hL hc hb).seq ?_
  refine (two_wpAt (Ψ := CW w k) (cp_rel agreeCA) fun L g m₀ y t hL hc h => copyW_ok hL hc h).seq ?_
  -- `update` of `T(k)`
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧ WS w L m₀ u.mem (fun _ => []) ∧
      UR (BitVec.ofNat 32 (w.F.H.B + 0)) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eT) (pl w k) L m₀ u)
    (two_prog [.esp] espOnly updT_taint) fun L g m₀ y t hL hc ⟨hb, hw⟩ =>
      WP.mono (updT_ok hL hc hb) fun u ⟨cu, ru, mu⟩ => ⟨cu, hb.mem mu, by rw [mu]; exact hw, ru⟩).seq ?_
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧
      WS w L m₀ u.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k)
    (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintE tblk2_taint1 tfn_upd
      (fun _ _ _ _ ⟨hb, hw, hr⟩ hk hm _ => ⟨hb.mem hm, by rw [hm]; exact hw, hr.keep hk⟩)
      (upd_rel' fun L g m₀ y u hL hc ⟨hb, _, hr⟩ => argsT hL hc hb hr))
    fun L g m₀ y t hL hc ⟨hb, hw, hr⟩ => callT_ok hL hc hb hw hr).seq ?_
  -- `update` of `info`
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧
      (WS w L m₀ u.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k) ∧
      UR (BitVec.ofNat 32 (w.F.H.B + pl w k)) (L.a 1) (L.a 2).toNat L m₀ u)
    (two_prog [.esp] espOnly updI_taint) fun L g m₀ y t hL hc ⟨hb, hw⟩ =>
      WP.mono (updI_ok hL hc hb) fun u ⟨cu, ru, mu⟩ => ⟨cu, hb.mem mu, by rw [mu]; exact hw, ru⟩).seq ?_
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧
      WS w L m₀ u.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀)
    (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintE tblk2_taint1 tfn_upd
      (fun _ _ _ _ ⟨hb, hw, hr⟩ hk hm _ => ⟨hb.mem hm, by rw [hm]; exact hw, hr.keep hk⟩)
      (upd_rel' fun L g m₀ y u hL hc ⟨hb, _, hr⟩ => argsI hL hc hb hr))
    fun L g m₀ y t hL hc ⟨hb, hw, hr⟩ => callI_ok hL hc hb hw hr).seq ?_
  -- `update` of the counter's byte
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧
      (WS w L m₀ u.mem fun prk => Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀) ∧
      UR (BitVec.ofNat 32 (w.F.H.B + (pl w k + (L.a 2).toNat))) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC) 1
        L m₀ u ∧
      Spec.Sha256.bytesAt u.mem ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.eC).setWidth 64) 1 = [BitVec.ofNat 8 (k + 1)])
    (two_prog [.esp] espOnly updC_taint) fun L g m₀ y t hL hc ⟨hb, hw⟩ =>
      WP.mono (updC_ok hL hc hb hw) fun u ⟨cu, ru, bu, wu, yu⟩ => ⟨cu, bu, wu, ru, yu⟩).seq ?_
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧
      WS w L m₀ u.mem fun prk =>
        Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ ++ [BitVec.ofNat 8 (k + 1)])
    (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintE tblk2_taint1 tfn_upd
      (fun _ _ _ _ ⟨hb, hw, hr, hy⟩ hk hm _ => ⟨hb.mem hm, by rw [hm]; exact hw, hr.keep hk, by rw [hm]; exact hy⟩)
      (upd_rel' fun L g m₀ y u hL hc ⟨hb, _, hr, _⟩ => argsC hL hc hb hr))
    fun L g m₀ y t hL hc ⟨hb, hw, hr, hy⟩ => callC_ok hL hc hb hw hr hy).seq ?_
  -- `finalize`
  refine (two_wpAt (Ψ := fun L m₀ u => BI w k L m₀ u ∧
      (WS w L m₀ u.mem fun prk =>
        Proof.Hkdf.tBlock w.ok.hH.SH.H prk (infoOf L m₀) k ++ infoOf L m₀ ++ [BitVec.ofNat 8 (k + 1)]) ∧
      FA w k L m₀ u)
    (two_prog [.esp] espOnly finT_taint) fun L g m₀ y t hL hc ⟨hb, hw⟩ =>
      WP.mono (finT_ok hL hc hb) fun u ⟨cu, au, mu⟩ => ⟨cu, hb.mem mu, by rw [mu]; exact hw, au⟩).seq ?_
  refine (two_wpAt (Ψ := BF w k)
    (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintE tblk2_taint2 tfn_fin
      (fun _ _ _ _ ⟨hb, hw, a1, a2, a3, a4, a5, a6⟩ hk hm _ => ⟨hb.mem hm, by rw [hm]; exact hw,
        (hk _ (by decide)).trans a1, (hk _ (by decide)).trans a2, (hk _ (by decide)).trans a3,
        (hk _ (by decide)).trans a4, (hk _ (by decide)).trans a5, (hk _ (by decide)).trans a6⟩)
      (fin_rel fun L g m₀ y u hL hc ⟨hb, _, ha⟩ => finE hL hb.1 hc ha))
    fun L g m₀ y t hL hc ⟨hb, hw, ha⟩ => callF_ok hL hc hb hw ha).seq ?_
  -- the output
  refine (outLen_rel e).seq ?_
  refine (two_wpAt (Ψ := OA w k) (two_prog [.esp] espOnly outA_taint) fun L g m₀ y t hL hc ⟨hb, hx⟩ =>
    WP.mono (outA_ok hL hc hb hx) fun u ⟨cu, mu, d, b, s, x, _⟩ => ⟨cu, hb.mem mu, d, b, s, x⟩).seq ?_
  refine (two_wpAt (Ψ := NB w k) (cp_rel agreeOA) fun L g m₀ y t hL hc ⟨hb, d, b, s, x⟩ =>
    outCp_ok hL hc hb d b s x).seq ?_
  exact two_wpAt (two_prog [.esp] espOnly next_taint) fun L g m₀ y t hL hc h => nextB_ok hL hc h

/-- Two runs of the blocks, with the same layout. -/
theorem loop_rel (e : Env2 eSh) :
    RelCT isa (fun a b => TwoAt ⟨w, f⟩ (EI w 0) e a b ∧ isa.eval .ne a = some true)
      (.loop (Impl.Hkdf.X86.block f) .ne) (Two (S := eSh) ⟨w, f⟩ fun _ _ _ => True) := by
  refine (RelCT.loop (I := fun n (a b : State) => ∃ k, n = olen e.L - k * w.F.H.D ∧ olen e.L - done w e.L k ≠ 0 ∧
    TwoAt ⟨w, f⟩ (EI w k) e a b) (fun n => ?_) (olen e.L)).mono (fun a b ⟨h, hev⟩ => ⟨0, by
      rw [Nat.zero_mul, Nat.sub_zero], ?_, h⟩) fun _ _ h => h
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hs, hL, c₁, c₂, f₁, f₂⟩ x₁ x₂
    have hD0 : 0 < w.F.H.D := (esizes f₁.1).2.2.2.2.2.2.1
    have hlt := (ei_bi f₁ hs).2.1
    obtain ⟨ht, hL', c₁', c₂', f₁', f₂'⟩ :=
      block_rel k e s₁ s₂ t₁ t₂ s₁' s₂' ⟨hL, c₁, c₂, ei_bi f₁ hs, ei_bi f₂ hs⟩ x₁ x₂
    refine ⟨ht, by rw [show isa.eval .ne s₁' = _ from eval_ne f₁', show isa.eval .ne s₂' = _ from eval_ne f₂'],
      fun _ => ⟨e, hL', c₁', c₂', trivial, trivial⟩, fun hev => ?_⟩
    rw [show isa.eval .ne s₁' = _ from eval_ne f₁', Option.some.injEq, decide_eq_true_eq] at hev
    have hd : done w e.L (k + 1) = (k + 1) * w.F.H.D := by
      refine Nat.min_eq_left (Nat.le_of_not_le fun hc => hev ?_)
      rw [show done w e.L (k + 1) = olen e.L from Nat.min_eq_right hc, Nat.sub_self]
    have hsm : (k + 1) * w.F.H.D = k * w.F.H.D + w.F.H.D := Nat.succ_mul _ _
    rw [hd] at hev
    exact ⟨olen e.L - (k + 1) * w.F.H.D, by omega, k + 1, rfl, by rw [hd]; exact hev, hL', c₁', c₂', f₁', f₂'⟩
  · rw [show isa.eval .ne a = _ from eval_ne h.2.2.2.1, Option.some.injEq, decide_eq_true_eq] at hev
    exact hev

/-- Two runs of the frame's body, from calls whose public data agree. -/
theorem expandBody_rel (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) {s₁ s₂ : State}
    (h : (expandR w f ns eStack).pre s₁ ∧ (expandR w f ns eStack).pre s₂ ∧ (expandR w f ns eStack).pub s₁ s₂) :
    RelCT isa (fun a b => a = allocFrame eSh.FB s₁ ∧ b = allocFrame eSh.FB s₂) (Impl.Hkdf.X86.expandBody f)
      fun _ _ => True := by
  obtain ⟨hL, hx⟩ := layE_ok hw h.1
  have he₁ := entryE h.1
  have he₂ := entryE (w := w) h.2.1
  rw [layE_eq hns h.2.2] at he₂
  unfold Impl.Hkdf.X86.expandBody
  refine (start_rel (K := ⟨w, f⟩) hL (P := EOk w) hx he₁ he₂ entry_taintE).seq ?_
  refine two_exists fun e => ?_
  refine (two_wpAt (Ψ := EI w 0) (two_prog _ agreeEax etab_taint)
    fun L g m₀ y t hL hc h => etab_ok hL hc h).seq (RelCT.seq ?_ (two_prog (K := ⟨w, f⟩) (S := eSh) (Φ := fun _ _ _ => True) [.esp] espOnly restore_taint))
  refine RelCT.ite (fun a b ⟨_, _, _, f₁, f₂⟩ => by
    rw [show isa.eval .ne a = _ from eval_ne f₁, show isa.eval .ne b = _ from eval_ne f₂]) (loop_rel e) ?_
  exact (two_wp (Ψ := fun _ _ _ => True) (two_prog [.esp] espOnly nil_taint)
    fun _ _ _ _ _ _ hc _ => WP.block_nil ⟨hc, trivial⟩).mono (fun a b ⟨h, _⟩ => ⟨e, h⟩) fun _ _ h => h

/-- `vg_hkdf_expand` is constant time: two runs whose public data agree have
the same layout, and leak the same trace. -/
theorem expand_ct (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) :
    ConstantTime isa (expandR w f ns eStack).pre (expandR w f ns eStack).pub (Impl.Hkdf.X86.expand f) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.frameAlloc (R := fun _ _ => True)
    ((VG.RelCT.exists_ fun q : State × State => VG.RelCT.exists_ fun h : (expandR w f ns eStack).pre q.1 ∧
      (expandR w f ns eStack).pre q.2 ∧ (expandR w f ns eStack).pub q.1 q.2 => expandBody_rel hw hns h).mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨(s₁, s₂), h, ea, eb⟩) fun _ _ h => h))

end

end VG.Proof.Hkdf.X86
