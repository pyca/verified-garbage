module

public import VerifiedGarbage.Proof.Hkdf.X86.Env
public import VerifiedGarbage.Proof.Hkdf.X86.Key
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
# HKDF on x86 (32-bit): `vg_hkdf_extract`, correct and constant time

The contract the proof is written against (`extractR`), for the table
`hmac` of one variant `w` (`HVar`), whose functions an indirect call of
`f`'s reaches: `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`
writes `HMAC(salt, IKM)` to `prk`, which is `D` bytes long. In its frame
(`xFr` bytes: our caller's registers, `B`, HMAC's inner and outer states,
then the working space), the entry copies `B` from the table to the frame
(`xtab_ok`); then `init` with the salt as the key (`xinit_ok`), `update`
with the input keying material (`xupd_ok`) and `finalize` into `prk`
(`xfin_ok`), each through the table, from its arguments (`XIA`, `XUA`,
`XFA`); then our caller's registers back. The count `B + ikm_len` fits 32
bits, the input keying material being apart from the stack in the 32-bit
address space (`ikm_lt`). Two runs whose public data agree have the same
layout (`layX`), and each piece is related in them (`extract_ct`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86

open VG VG.X86 VG.X86.Wp
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.HmacTable.X86 (HVar TabOK TabMem)
open VG.Proof.Pbkdf2.Whole.X86 (HfArgs)
open VG.Proof.Pbkdf2.Whole.X86.Any (AnyArgs)
open VG.Proof.Pbkdf2.Stream.X86 (UpdArgs)

/-! ## The contract -/

/-- The stack `vg_hkdf_extract` uses: its frame, and the 100 bytes below it
the call of `init` uses. -/
def xStack : Nat := Impl.Hkdf.X86.xFr + 100

/-- `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`, with `N`
bytes of stack, for the table `hmac` of `w`, whose functions an indirect
call of `f`'s reaches, with the addresses of the functions `ns` public. -/
def extractR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let salt : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let ikm : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let prk : Region := ⟨(arg s 4).setWidth 64, w.F.H.D⟩
    let tab : Region := ⟨(arg s 6).setWidth 64, 24⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32 ∧
      s.rd = [salt, ikm, tab] ∧ s.wr = [prk, args] ∧
      salt.Disjoint prk ∧ ikm.Disjoint prk ∧ prk.Disjoint tab ∧ prk.Disjoint args ∧ ret.Disjoint prk ∧
      stk.Disjoint salt ∧ stk.Disjoint ikm ∧ stk.Disjoint prk ∧ stk.Disjoint tab ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
      (arg s 4).toNat + w.F.H.D ≤ 2 ^ 32 ∧ (arg s 6).toNat + 24 ≤ 2 ^ 32 ∧ TabFacts w f s (arg s 6)
  post s s' := Spec.Sha256.bytesAt s'.mem ((arg s 4).setWidth 64) w.F.H.D =
    Spec.Hkdf.extract w.ok.hH.SH.H (Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
      (Spec.Sha256.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 7, arg s₁ i = arg s₂ i) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-! ## The layout -/

/-- `extract`'s frame: 3812 bytes, 100 below it, seven arguments, the table the last. -/
def xSh : Sh := ⟨Impl.Hkdf.X86.xFr, 100, 7, 6⟩

/-- The layout of a call from `s`. -/
def layX (w : HVar) (s : State) : Lay xSh where
  E := s.gpr .esp
  a i := if i < 7 then arg s i else 0
  W := ⟨(arg s 4).setWidth 64, w.F.H.D⟩
  rd := [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
    ⟨(arg s 6).setWidth 64, 24⟩]
  wr := [⟨(arg s 4).setWidth 64, w.F.H.D⟩, ⟨argAddr s 0, 28⟩]
  fa := faOf w s

/-- What `extract` needs of the layout besides `Lay.Ok`: the salt's and the
input keying material's places, and the variant's sizes. -/
structure XOk (w : HVar) (L : Lay xSh) : Prop where
  hw : HOk w
  W : L.W = ⟨(L.a 4).setWidth 64, w.F.H.D⟩
  sRd : (⟨(L.a 0).setWidth 64, (L.a 1).toNat⟩ : Region) ∈ L.rd
  iRd : (⟨(L.a 2).setWidth 64, (L.a 3).toNat⟩ : Region) ∈ L.rd
  sW : Region.Disjoint ⟨(L.a 0).setWidth 64, (L.a 1).toNat⟩ L.W
  iW : Region.Disjoint ⟨(L.a 2).setWidth 64, (L.a 3).toNat⟩ L.W
  kS : L.STK.Disjoint ⟨(L.a 0).setWidth 64, (L.a 1).toNat⟩
  kI : L.STK.Disjoint ⟨(L.a 2).setWidth 64, (L.a 3).toNat⟩
  ns : (L.a 0).toNat + (L.a 1).toNat ≤ 2 ^ 32
  ni : (L.a 2).toNat + (L.a 3).toNat ≤ 2 ^ 32
  np : (L.a 4).toNat + w.F.H.D ≤ 2 ^ 32

section
variable {w : HVar} {f : Fns} {ns : List String}

theorem layX_a {s : State} {i : Nat} (hi : i < 7) : (layX w s).a i = arg s i := by
  simp only [layX, hi, ite_true]

/-- The layout of a call meeting the contract. -/
theorem layX_ok {s : State} (hw : HOk w) (hp : (extractR w f ns xStack).pre s) :
    (layX w s).Ok ∧ XOk w (layX w s) := by
  obtain ⟨hsp, htop, hrd, hwr, sp', ip, pt, pa, rp, ks, ki, kp, kt, ns', ni, np, nt, -⟩ := hp
  have hB : (layX w s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 xSh.N := B_eq' hsp
  have eK : (layX w s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 xStack, xStack⟩ := by
    show (⟨(layX w s).B, xSh.N⟩ : Region) = _; rw [hB]; rfl
  have eR : (layX w s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show (⟨(layX w s).B + BitVec.ofNat 64 xSh.N, 4⟩ : Region) = _; rw [hB, BitVec.sub_add_cancel]
  have eA : (layX w s).ARGS = ⟨argAddr s 0, 28⟩ := by
    show (⟨(layX w s).B + BitVec.ofNat 64 (xSh.N + 4), 4 * 7⟩ : Region) = _
    rw [hB, ← Offset.add_add ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 xSh.N) xSh.N 4, BitVec.sub_add_cancel]
    show (⟨(s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4, 28⟩ : Region) =
      ⟨(s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 28⟩
    rw [show 4 + 4 * 0 = 4 from rfl, ← addr, addr_eq (by omega_arith)]
  have a0 := layX_a (w := w) (s := s) (i := 0) (by decide)
  have a1 := layX_a (w := w) (s := s) (i := 1) (by decide)
  have a2 := layX_a (w := w) (s := s) (i := 2) (by decide)
  have a3 := layX_a (w := w) (s := s) (i := 3) (by decide)
  have a4 := layX_a (w := w) (s := s) (i := 4) (by decide)
  refine ⟨⟨hsp, by show (s.gpr .esp).toNat + 4 + 4 * 7 ≤ 2 ^ 32; omega_arith, by decide, by decide, by decide,
    by decide, by decide, ?_, by rw [eK]; exact kp, by rw [eR]; exact rp, by rw [eA]; exact pa.symm, nt, pt.symm,
    by rw [eK]; exact kt.symm, ?_, ?_, ?_⟩, ⟨hw, by rw [a4]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show (BitVec.setWidth 64 (arg s 4)).toNat + w.F.H.D ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega_arith)]; exact np
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  · rw [eA]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  · exact List.mem_cons_self
  · rw [a0, a1]; exact List.mem_cons_self
  · rw [a2, a3]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [a0, a1]; exact sp'
  · rw [a2, a3]; exact ip
  · rw [eK, a0, a1]; exact ks
  · rw [eK, a2, a3]; exact ki
  · rw [a0, a1]; exact ns'
  · rw [a2, a3]; exact ni
  · rw [a4]; exact np

/-- What the contract says on entry, with the layout. -/
theorem entryX {s : State} (hp : (extractR w f ns xStack).pre s) : Entry ⟨w, f⟩ (layX w s) s := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, tok, tm, td, tb⟩ := hp
  exact ⟨rfl, hrd, hwr, fun i hi => by have hi' : i < 7 := hi; simp only [layX, hi', ite_true],
    tok, tm, td, tb, fun n hn => by simp only [layX, faOf, hn, ite_true]⟩

end

/-! ## The pieces -/

section
variable {w : HVar} {f : Fns} {L : Lay xSh} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32}

theorem xconsts : Impl.Hkdf.X86.xB = 16 ∧ Impl.Hkdf.X86.xIn = 20 ∧ Impl.Hkdf.X86.xOut = 212 ∧
    Impl.Hkdf.X86.xWork = 404 ∧ xSh.FB = 3812 ∧ xSh.cb = 100 ∧ xSh.NA = 7 ∧ xSh.N = 3912 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The frame's copy of `B`. -/
abbrev XBw (w : HVar) (L : Lay xSh) (m : Mem) : Prop :=
  m.readW (L.B + BitVec.ofNat 64 (xSh.cb + Impl.Hkdf.X86.xB)) 32 = BitVec.ofNat 32 w.F.H.B

/-- `B` from the table to the frame. -/
theorem xtab_ok (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hax : u.gpr .eax = L.tb) :
    WP isa (.block Impl.Hkdf.X86.extractTab) u fun u' => Ctx ⟨w, f⟩ L g m₀ y u' ∧ XBw w L u'.mem ∧
      u'.syms = u.syms := by
  rw [Impl.Hkdf.X86.extractTab, show ([.mov .ecx (.mem (Impl.Pbkdf2.Stream.X86.at_ .eax 20)),
    .store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.xB) .ecx] : List Instr) =
      [.mov .ecx (.mem (Impl.Pbkdf2.Stream.X86.at_ .eax 20))] ++ [.store (Impl.Hkdf.X86.sp Impl.Hkdf.X86.xB) .ecx]
    from rfl, WP.block_append_iff]
  refine WP.mono (tabld_ok hL hc (d := .ecx) (by decide) hax (o := 20) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (stF_ok hL h₁.ctx .ecx (o := Impl.Hkdf.X86.xB) (by decide) (by decide)) fun u₂ ⟨c₂, hm, hg, hs⟩ => ?_
  refine ⟨c₂, ?_, hs.trans h₁.syms⟩
  rw [XBw, hm, Mem.readW_writeW_self32, h₁.val, hc.tabB]

/-- The frame's copy of `B` is kept by writes apart from it. -/
theorem XBw.keep {m m' : Mem} (hb : XBw w L m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 (xSh.cb + Impl.Hkdf.X86.xB), 4⟩ r) : XBw w L m' := by
  rw [XBw, hf.readW (Region.contains_self _ _) hd (by decide)]; exact hb

/-- `init`'s arguments. -/
def XIA : Pr xSh := fun L _ u =>
  u.gpr .edi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn ∧ u.gpr .esi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xOut ∧
    u.gpr .edx = L.a 0 ∧ u.gpr .ecx = L.a 1 ∧ u.gpr .ebp = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xWork

theorem xinitA_ok (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) :
    WP isa (.block Impl.Hkdf.X86.extractInit) u fun u' => Ctx ⟨w, f⟩ L g m₀ y u' ∧ XIA L m₀ u' ∧
      u'.mem = u.mem ∧ u'.syms = u.syms := by
  rw [Impl.Hkdf.X86.extractInit, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edi) (by decide) Impl.Hkdf.X86.xIn) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .esi) (by decide) Impl.Hkdf.X86.xOut) fun u₂ h₂ => ?_
  rw [show ([.mov .edx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.xFr 0), .mov .ecx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.xFr 1)] :
      List Instr) = [.mov .edx (Impl.Hkdf.X86.argM xSh.FB 0)] ++ [.mov .ecx (Impl.Hkdf.X86.argM xSh.FB 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (arg_ok hL h₂.ctx (d := .edx) (by decide) (i := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (arg_ok hL h₃.ctx (d := .ecx) (by decide) (i := 1) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (fr_ok hL h₄.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.xWork) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, ⟨?_, ?_, ?_, ?_, h₅.val⟩, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [h₅.syms, h₄.syms, h₃.syms, h₂.syms, h₁.syms]⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- Facts of the sizes, for `omega`. -/
theorem xsizes (hx : XOk w L) : w.ok.hH.SH.stateBytes ≤ 192 ∧ w.F.H.S ≤ 192 ∧ (w.F.W + w.F.H.S) * 8 ≤ 3408 ∧
    w.ok.Wf * 8 ≤ 1872 ∧ w.ok.hH.Wb ≤ 1872 ∧ w.ok.hH.SH.digestBytes = w.F.H.D ∧ w.F.H.D ≤ 64 := by
  have h := hx.hw
  exact ⟨by rw [w.ok.hH.hS]; exact h.2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, w.ok.hH.hD, h.2.2.2.2.2⟩

/-- `init`'s regions. -/
theorem anyX (hL : L.Ok) (hx : XOk w L) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (ha : XIA L m₀ u) :
    AnyArgs w.ok.hH.SH (w.F.W + w.F.H.S) u (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xOut) (L.a 0) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xWork)
      (L.a 1).toNat := by
  obtain ⟨hdi, hsi, hdx, hcx, hbp⟩ := ha
  obtain ⟨hS, -, hA, -⟩ := xsizes hx
  have e3 : xSh.FB = 3812 := rfl
  have e4 : xSh.cb = 100 := rfl
  have e5 : xSh.NA = 7 := rfl
  have hb : Proof.Pbkdf2.Whole.X86.Any.stk100 u = L.CALLS := by
    show below (u.gpr .esp) 100 = _; rw [hc.esp]; exact hL.below_F_eq
  have hFN := hL.FN; have := hL.e0; have := hL.e1; have := xSh.N_eq
  have c1 : Impl.Hkdf.X86.xIn = 20 := rfl
  have c2 : Impl.Hkdf.X86.xOut = 212 := rfl
  have c3 : Impl.Hkdf.X86.xWork = 404 := rfl
  exact
    { edi := hdi, esi := hsi, edx := hdx
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      ebp := hbp
      kl32 := (L.a 1).isLt
      sp := by rw [hc.esp, hL.FN]; omega_arith
      cr := VG.Covers.left (by
        rw [hc.rd]; exact VG.Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hx.sRd)
      cw := by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xIn, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xOut, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xWork, hL.frBase (by decide), by dsimp only; omega_arith⟩
      i_o := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      i_k := hx.kS.sub_left (hL.fr_sub (by omega_arith))
      i_s := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      o_k := (hx.kS.sub_left (hL.fr_sub (by omega_arith)))
      o_s := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      k_s := (hx.kS.sub_left (hL.fr_sub (by omega_arith))).symm
      b_i := by rw [hb]; exact hL.calls_fr (by omega_arith)
      b_o := by rw [hb]; exact hL.calls_fr (by omega_arith)
      b_k := by rw [hb]; exact hx.kS.sub_left Lay.Ok.calls_stk
      b_s := by rw [hb]; exact hL.calls_fr (by omega_arith)
      ni := by rw [hL.frN (by decide)]; omega_arith
      no := by rw [hL.frN (by decide)]; omega_arith
      nk := hx.ns
      nsc := by rw [hL.frN (by decide)]; omega_arith }

/-- HMAC's states for the salt's block key `k0`. -/
abbrev XI (w : HVar) (L : Lay xSh) (m₀ : Mem) (msg : List Byte) (m : Mem) : Prop :=
  w.ok.hH.SH.Repr m ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn).setWidth 64)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey w.ok.hH.SH.H (Spec.Sha256.bytesAt m₀ ((L.a 0).setWidth 64) (L.a 1).toNat))
        Spec.Hmac.ipad ++ msg) ∧
    w.ok.hH.SH.Repr m ((L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xOut).setWidth 64)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey w.ok.hH.SH.H (Spec.Sha256.bytesAt m₀ ((L.a 0).setWidth 64) (L.a 1).toNat))
        Spec.Hmac.opad)

/-- The bytes of a buffer only read are those on entry. -/
theorem Ctx.readBytes {S : Sh} {K : Hk} {L : Lay S} {t : State} (hc : Ctx K L g m₀ y t) {p : BitVec 32} {n : Nat}
    (hW : Region.Disjoint ⟨p.setWidth 64, n⟩ L.W) (hK : L.STK.Disjoint ⟨p.setWidth 64, n⟩) (hn : n < 2 ^ 32) :
    Spec.Sha256.bytesAt t.mem (p.setWidth 64) n = Spec.Sha256.bytesAt m₀ (p.setWidth 64) n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi =>
    hc.bytes (R := ⟨p.setWidth 64, n⟩) hW hK.symm (by show n ≤ 2 ^ 64; omega_arith) (List.mem_range.mp hi)

/-- `init` through the table. -/
theorem xinit_ok (hL : L.Ok) (hx : XOk w L) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (ha : XIA L m₀ t)
    (hb : XBw w L t.mem) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.xFr 6 0 f.init Impl.Ecdsa.Rfc6979.X86.init5) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ XBw w L u.mem ∧ XI w L m₀ [] u.mem := by
  refine tcall_ok (K := ⟨w, f⟩) hL hc (j := 0) (by decide) (by rw [Nat.mul_zero]; exact hc.tabMem.1) hc.tabOk.i
    fun t' c' hm' hk' _ => ?_
  have ha' : XIA L m₀ t' := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := ha
    exact ⟨(hk' _ (by decide)).trans a1, (hk' _ (by decide)).trans a2, (hk' _ (by decide)).trans a3,
      (hk' _ (by decide)).trans a4, (hk' _ (by decide)).trans a5⟩
  obtain ⟨hS, -, hA, -⟩ := xsizes hx
  obtain ⟨c0, c1, c2, c3, e3, e4, e5, e6⟩ := xconsts
  refine WP.mono (init_wp hL c' (anyX hL hx c' ha') (by decide) fun r hr => ?_) fun u ⟨cu, _, hf, hi, ho⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact .inr (.inl (hL.fr_hi (by decide) (by omega_arith)))
  · refine ⟨cu, ?_, ?_⟩
    · refine (hm' ▸ hb).keep hf fun r hr => ?_
      have := xSh.N_eq; have := hL.nB
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact hL.fr_disj (.inl (by decide)) (by decide) (by omega_arith)
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact hL.fr_disj (.inl (by decide)) (by decide) (by omega_arith)
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact hL.fr_disj (.inl (by decide)) (by decide) (by omega_arith)
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact (hL.calls_fr (by decide)).symm
    · rw [c'.readBytes hx.sW hx.kS (L.a 1).isLt] at hi ho
      exact ⟨by rw [List.append_nil]; exact hi, ho⟩


/-- HMAC's key, its block size. -/
theorem blockKey_length' (w : HVar) (k : List Byte) : (Spec.Hmac.blockKey w.ok.hH.SH.H k).length = w.F.H.B := by
  have hB := w.ok.hH.hB
  have hDB := w.ok.hDB
  simp only [Spec.Hmac.blockKey, hB, List.length_append, List.length_replicate]
  split
  · have := w.hlen k; omega_arith
  · omega_arith

/-- The input keying material's bytes. -/
abbrev ikmOf (L : Lay xSh) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ ((L.a 2).setWidth 64) (L.a 3).toNat

/-- The count `B + ikm_len` fits 32 bits: the input keying material is apart
from the stack, in the 32-bit address space. -/
theorem ikm_lt (hL : L.Ok) (hx : XOk w L) : w.F.H.B + (L.a 3).toNat < 2 ^ 32 := by
  have h := VG.Proof.Pbkdf2.Whole.len_add_le hx.kI (N := 2 ^ 32) (by have := hL.nB; dsimp only; omega_arith)
    (by dsimp only; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (L.a 2).isLt; omega_arith)]; exact hx.ni)
  have hB : w.F.H.B ≤ 128 := w.ok.hH.hBB
  obtain ⟨-, -, -, -, -, -, -, e6⟩ := xconsts
  dsimp only at h
  omega_arith

/-- `update`'s arguments. -/
def XUA (w : HVar) : Pr xSh := fun L _ u =>
  u.gpr .edi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn ∧ u.gpr .esi = BitVec.ofNat 32 w.F.H.B ∧ u.gpr .eax = 0 ∧
    u.gpr .edx = L.a 2 ∧ u.gpr .ecx = L.a 3 ∧ u.gpr .ebp = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xWork

theorem xupdA_ok (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hb : XBw w L u.mem) :
    WP isa (.block Impl.Hkdf.X86.extractUpd) u fun u' => Ctx ⟨w, f⟩ L g m₀ y u' ∧ XUA w L m₀ u' ∧
      u'.mem = u.mem ∧ u'.syms = u.syms := by
  rw [Impl.Hkdf.X86.extractUpd, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edi) (by decide) Impl.Hkdf.X86.xIn) fun u₁ h₁ => ?_
  rw [show ([.mov .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.xB)), .mov .eax (.imm 0),
      .mov .edx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.xFr 2), .mov .ecx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.xFr 3)] :
      List Instr) = [.mov .esi (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.xB))] ++ [.mov .eax (.imm 0)] ++
      [.mov .edx (Impl.Hkdf.X86.argM xSh.FB 2)] ++ [.mov .ecx (Impl.Hkdf.X86.argM xSh.FB 3)] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₁.ctx (d := .esi) (by decide) (o := Impl.Hkdf.X86.xB) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (movi_ok hL h₂.ctx (d := .eax) (by decide) 0) fun u₃ h₃ => ?_
  refine WP.mono (arg_ok hL h₃.ctx (d := .edx) (by decide) (i := 2) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (arg_ok hL h₄.ctx (d := .ecx) (by decide) (i := 3) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (fr_ok hL h₅.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.xWork) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, ⟨?_, ?_, ?_, ?_, ?_, h₆.val⟩, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [h₆.syms, h₅.syms, h₄.syms, h₃.syms, h₂.syms, h₁.syms]⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val,
      h₁.mem]; exact hb
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

/-- `update`'s regions. -/
theorem updX (hL : L.Ok) (hx : XOk w L) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (ha : XUA w L m₀ u) :
    UpdArgs w.ok.hH u .esi .edi (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn) (L.a 2)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xWork) (BitVec.ofNat 32 w.F.H.B) (L.a 3).toNat := by
  obtain ⟨hdi, hsi, hax, hdx, hcx, hbp⟩ := ha
  obtain ⟨-, hS, -, -, hWb, -⟩ := xsizes hx
  obtain ⟨c0, c1, c2, c3, e3, e4, e5, e6⟩ := xconsts
  have hb : Region.Sub (Proof.Pbkdf2.Stream.X86.stk u) L.CALLS := sub_below hL hc (by decide)
  have hFN := hL.FN; have := hL.e0; have := hL.e1
  exact
    { hst := hdi, hlo := hsi, eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx, ebp := hbp, hr := by decide, hl := by decide
      hlen := (L.a 3).isLt
      sp48 := by rw [hc.esp, hL.FN]; omega_arith
      cd := VG.Covers.left (by
        rw [hc.rd]; exact VG.Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hx.iRd)
      cw := by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xIn, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xWork, hL.frBase (by decide), by dsimp only; omega_arith⟩
      st_sc := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      d_st := (hx.kI.sub_left (hL.fr_sub (by omega_arith))).symm
      d_sc := (hx.kI.sub_left (hL.fr_sub (by omega_arith))).symm
      b_st := (hL.calls_fr (by omega_arith)).sub_left hb
      b_d := (hx.kI.sub_left Lay.Ok.calls_stk).sub_left hb
      b_sc := (hL.calls_fr (by omega_arith)).sub_left hb
      nst := by rw [hL.frN (by decide)]; omega_arith
      nd := hx.ni
      nsc := by rw [hL.frN (by decide)]; omega_arith }

/-- `update` through the table: the inner state holds the input keying material too. -/
theorem xupd_ok (hL : L.Ok) (hx : XOk w L) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (ha : XUA w L m₀ t)
    (hb : XBw w L t.mem) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.xFr 6 1 f.upd Impl.Ecdsa.Rfc6979.X86.upd6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ XBw w L u.mem ∧ (XI w L m₀ [] t.mem → XI w L m₀ (ikmOf L m₀) u.mem) := by
  refine tcall_ok (K := ⟨w, f⟩) hL hc (j := 1) (by decide) hc.tabMem.2.1 hc.tabOk.u fun t' c' hm' hk' _ => ?_
  have ha' : XUA w L m₀ t' := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
    exact ⟨(hk' _ (by decide)).trans a1, (hk' _ (by decide)).trans a2, (hk' _ (by decide)).trans a3,
      (hk' _ (by decide)).trans a4, (hk' _ (by decide)).trans a5, (hk' _ (by decide)).trans a6⟩
  obtain ⟨hS', hS, -, -, hWb, -⟩ := xsizes hx
  obtain ⟨c0, c1, c2, c3, e3, e4, e5, e6⟩ := xconsts
  have := xSh.N_eq; have := hL.nB
  refine WP.mono (upd_wp hL c' (updX hL hx c' ha') fun r hr => ?_) fun u ⟨cu, _, hf, hR⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact .inr (.inl (hL.fr_hi (by decide) (by omega_arith)))
  · refine ⟨cu, (hm' ▸ hb).keep hf ?kp, fun hI => ?xi⟩
    case kp =>
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact hL.fr_disj (.inl (by decide)) (by decide) (by omega_arith)
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact hL.fr_disj (.inl (by decide)) (by decide) (by omega_arith)
      · rw [← hL.frv (o := Impl.Hkdf.X86.xB) (by decide)]; exact (hL.calls_fr (by decide)).symm
    case xi =>
      obtain ⟨hi, ho⟩ := hI
      refine ⟨?_, ?_⟩
      · have h1 := hR _ (by rw [hm']; exact hi) (by
          rw [List.append_nil, VG.Proof.Hmac.Common.xorPad_length, blockKey_length' (w := w),
            Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by have := w.ok.hH.hBB; omega_arith)])
        rw [c'.readBytes hx.iW hx.kI (L.a 3).isLt, List.append_nil] at h1
        exact h1
      · refine w.ok.hH.repr t'.mem u.mem _ _ _ (fun i hi' => ?_) (by rw [hm']; exact ho)
        refine hf.bytes (R := ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xOut).setWidth 64, w.F.H.S⟩) (fun r hr => ?_)
          (by dsimp only; omega_arith) hi'
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.fr_disj (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
        · exact hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
        · exact (hL.calls_fr (by omega_arith)).symm

/-- `finalize`'s arguments. -/
def XFA (w : HVar) : Pr xSh := fun L _ u =>
  u.gpr .edx = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn ∧ u.gpr .esi = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xOut ∧
    u.gpr .eax = BitVec.ofNat 32 w.F.H.B + L.a 3 ∧ u.gpr .ecx = 0 ∧ u.gpr .edi = L.a 4 ∧
    u.gpr .ebp = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xWork

theorem xfinA_ok (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (hb : XBw w L u.mem) :
    WP isa (.block Impl.Hkdf.X86.extractFin) u fun u' => Ctx ⟨w, f⟩ L g m₀ y u' ∧ XFA w L m₀ u' ∧
      u'.mem = u.mem ∧ u'.syms = u.syms := by
  rw [Impl.Hkdf.X86.extractFin, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edx) (by decide) Impl.Hkdf.X86.xIn) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .esi) (by decide) Impl.Hkdf.X86.xOut) fun u₂ h₂ => ?_
  rw [show ([.mov .eax (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.xB)), .alu .add .eax (Impl.Hkdf.X86.argM Impl.Hkdf.X86.xFr 3),
      .mov .ecx (.imm 0), .mov .edi (Impl.Hkdf.X86.argM Impl.Hkdf.X86.xFr 4)] : List Instr) =
      [.mov .eax (.mem (Impl.Hkdf.X86.sp Impl.Hkdf.X86.xB))] ++ [.alu .add .eax (Impl.Hkdf.X86.argM xSh.FB 3)] ++
      [.mov .ecx (.imm 0)] ++ [.mov .edi (Impl.Hkdf.X86.argM xSh.FB 4)] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL h₂.ctx (d := .eax) (by decide) (o := Impl.Hkdf.X86.xB) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (addA_ok hL h₃.ctx (d := .eax) (by decide) (i := 3) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (movi_ok hL h₄.ctx (d := .ecx) (by decide) 0) fun u₅ h₅ => ?_
  refine WP.mono (arg_ok hL h₅.ctx (d := .edi) (by decide) (i := 4) (by decide)) fun u₆ h₆ => ?_
  refine WP.mono (fr_ok hL h₆.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.xWork) fun u₇ h₇ => ?_
  refine ⟨h₇.ctx, ⟨?_, ?_, ?_, ?_, ?_, h₇.val⟩, by rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [h₇.syms, h₆.syms, h₅.syms, h₄.syms, h₃.syms, h₂.syms, h₁.syms]⟩
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide),
      h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide),
      h₃.keep _ (by decide), h₂.val]
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val, h₃.val, h₂.mem, h₁.mem]
    rw [hb]
  · rw [h₇.keep _ (by decide), h₆.keep _ (by decide), h₅.val]
  · rw [h₇.keep _ (by decide), h₆.val]

/-- `finalize`'s regions. -/
theorem finX (hL : L.Ok) (hx : XOk w L) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (ha : XFA w L m₀ u) :
    HfArgs w.ok.hH.SH w.ok.Wf u (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xIn) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xOut)
      (BitVec.ofNat 32 w.F.H.B + L.a 3) 0 (L.a 4) (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.xWork) := by
  obtain ⟨hdx, hsi, hax, hcx, hdi, hbp⟩ := ha
  obtain ⟨hS, -, -, hWf, -, hD, -⟩ := xsizes hx
  obtain ⟨c0, c1, c2, c3, e3, e4, e5, e6⟩ := xconsts
  have hb : Region.Sub (Proof.Pbkdf2.Whole.X86.stk u) L.CALLS := sub_below hL hc (by decide)
  have hFN := hL.FN; have := hL.e0; have := hL.e1
  have hO : Region.Sub ⟨(L.a 4).setWidth 64, w.ok.hH.SH.digestBytes⟩ L.W := by rw [hx.W, hD]; exact fun _ h => h
  exact
    { edx := hdx, esi := hsi, eax := hax, ecx := hcx, edi := hdi, ebp := hbp
      sp := by rw [hc.esp, hL.FN]; omega_arith
      cr := VG.Covers.right (by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xOut, hL.frBase (by decide), by dsimp only; omega_arith⟩)
      cw := by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xIn, hL.frBase (by decide), by dsimp only; omega_arith⟩
        · exact ⟨L.W, List.mem_cons_of_mem _ hL.wWr, 0, by rw [hx.W]; exact (BitVec.add_zero _).symm,
            by rw [hx.W]; dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, Impl.Hkdf.X86.xWork, hL.frBase (by decide), by dsimp only; omega_arith⟩
      i_u := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      i_o := (hL.fr_W (by omega_arith)).sub_right hO
      i_s := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      u_o := (hL.fr_W (by omega_arith)).sub_right hO
      u_s := hL.fr_disj (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      o_s := ((hL.fr_W (by omega_arith)).sub_right hO).symm
      b_i := (hL.calls_fr (by omega_arith)).sub_left hb
      b_u := (hL.calls_fr (by omega_arith)).sub_left hb
      b_o := (hL.calls_W.sub_right hO).sub_left hb
      b_s := (hL.calls_fr (by omega_arith)).sub_left hb
      ni := by rw [hL.frN (by decide)]; omega_arith
      nu := by rw [hL.frN (by decide)]; omega_arith
      no := by rw [hD]; exact hx.np
      nsc := by rw [hL.frN (by decide)]; omega_arith }


/-- `finalize` through the table: `PRK`. -/
theorem xfin_ok (hL : L.Ok) (hx : XOk w L) {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (ha : XFA w L m₀ t) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.xFr 6 2 f.fin Impl.Ecdsa.Rfc6979.X86.fin6) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ (XI w L m₀ (ikmOf L m₀) t.mem →
        Spec.Sha256.bytesAt u.mem ((L.a 4).setWidth 64) w.F.H.D =
          Spec.Hmac.hmacBlockKey w.ok.hH.SH.H
            (Spec.Hmac.blockKey w.ok.hH.SH.H (Spec.Sha256.bytesAt m₀ ((L.a 0).setWidth 64) (L.a 1).toNat))
            (ikmOf L m₀)) := by
  refine tcall_ok (K := ⟨w, f⟩) hL hc (j := 2) (by decide) hc.tabMem.2.2 hc.tabOk.f fun t' c' hm' hk' _ => ?_
  have ha' : XFA w L m₀ t' := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
    exact ⟨(hk' _ (by decide)).trans a1, (hk' _ (by decide)).trans a2, (hk' _ (by decide)).trans a3,
      (hk' _ (by decide)).trans a4, (hk' _ (by decide)).trans a5, (hk' _ (by decide)).trans a6⟩
  obtain ⟨hS, -, -, hWf, -, hD, -⟩ := xsizes hx
  obtain ⟨c0, c1, c2, c3, e3, e4, e5, e6⟩ := xconsts
  refine WP.mono (fin_wp hL c' (finX hL hx c' ha') fun r hr => ?_) fun u ⟨cu, _, _, hpost⟩ => ⟨cu, fun ⟨hi, ho⟩ => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (hL.fr_hi (by decide) (by omega_arith)))
    · exact .inl (by rw [hx.W, hD]; exact fun _ h => h)
    · exact .inr (.inl (hL.fr_hi (by decide) (by omega_arith)))
  · have hB := w.ok.hH.hB
    have hl := ikm_lt hL hx
    have hk0 := blockKey_length' w (Spec.Sha256.bytesAt m₀ ((L.a 0).setWidth 64) (L.a 1).toNat)
    have htl : (ikmOf L m₀).length = (L.a 3).toNat := VG.Proof.Hmac.Common.bytesAt_length _ _ _
    have e := hpost _ (ikmOf L m₀) (by rw [hk0, hB]) (by rw [hk0, htl]; omega_arith) (by rw [hm']; exact hi)
      (by
        rw [hB, htl, show BitVec.ofNat 32 w.F.H.B + L.a 3 = BitVec.ofNat 32 (w.F.H.B + (L.a 3).toNat) by
          rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
        exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat hl)
      (by rw [hm']; exact ho)
    rw [hD] at e
    exact e

/-- The frame's body of `vg_hkdf_extract`. -/
theorem extractBody_ok {s : State} (hL : (layX w s).Ok) (hx : XOk w (layX w s)) (he : Entry ⟨w, f⟩ (layX w s) s) :
    WP isa (Impl.Hkdf.X86.extractBody f) (allocFrame xSh.FB s) fun u =>
      Ctx ⟨w, f⟩ (layX w s) s.gpr s.mem s.syms u ∧ (∀ p ∈ Impl.Hkdf.X86.saved, u.gpr p.1 = s.gpr p.1) ∧
      Spec.Sha256.bytesAt u.mem ((arg s 4).setWidth 64) w.F.H.D =
        Spec.Hmac.hmacBlockKey w.ok.hH.SH.H
          (Spec.Hmac.blockKey w.ok.hH.SH.H (Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat))
          (Spec.Sha256.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) := by
  unfold Impl.Hkdf.X86.extractBody
  refine WP.seq (WP.mono (entry_ok hL he) fun t₁ ⟨c₁, ax⟩ => ?_)
  refine WP.seq (WP.mono (xtab_ok hL c₁ ax) fun t₂ ⟨c₂, hb₂, _⟩ => ?_)
  refine WP.seq (WP.mono (xinitA_ok hL c₂) fun t₃ ⟨c₃, ia, hm₃, _⟩ => ?_)
  refine WP.seq (WP.mono (xinit_ok hL hx c₃ ia (by rw [hm₃]; exact hb₂)) fun t₄ ⟨c₄, hb₄, xi₄⟩ => ?_)
  refine WP.seq (WP.mono (xupdA_ok hL c₄ hb₄) fun t₅ ⟨c₅, ua, hm₅, _⟩ => ?_)
  refine WP.seq (WP.mono (xupd_ok hL hx c₅ ua (by rw [hm₅]; exact hb₄)) fun t₆ ⟨c₆, hb₆, xi₆⟩ => ?_)
  refine WP.seq (WP.mono (xfinA_ok hL c₆ hb₆) fun t₇ ⟨c₇, fa, hm₇, _⟩ => ?_)
  refine WP.seq (WP.mono (xfin_ok hL hx c₇ fa) fun t₈ ⟨c₈, hp₈⟩ => ?_)
  refine WP.mono (restore_ok hL c₈) fun u ⟨cu, hr, hm⟩ => ⟨cu, hr, ?_⟩
  have e := hp₈ (by rw [hm₇]; exact xi₆ (by rw [hm₅]; exact xi₄))
  rw [ikmOf, layX_a (i := 4) (by decide), layX_a (i := 0) (by decide), layX_a (i := 1) (by decide),
    layX_a (i := 2) (by decide), layX_a (i := 3) (by decide)] at e
  rw [hm]; exact e

/-- `vg_hkdf_extract`: its frame, `B`, and HMAC's `init`, `update` and
`finalize` through the table. -/
theorem extract_correct {w : HVar} {f : Fns} {ns : List String} {s : State} (hw : HOk w)
    (hsp : NoSp (Impl.Hkdf.X86.extractBody f)) (hp : (extractR w f ns xStack).pre s) :
    WP isa (Impl.Hkdf.X86.extract f) s fun s' => abiPreserved s s' ∧ (extractR w f ns xStack).post s s' := by
  obtain ⟨hL, hx⟩ := layX_ok hw hp
  have he := entryX hp
  refine WP.mono (frame_ok hL he hsp (extractBody_ok hL hx he)) fun s' ⟨ha, u, hu, hm⟩ => ⟨ha, ?_⟩
  show Spec.Sha256.bytesAt s'.mem ((arg s 4).setWidth 64) w.F.H.D = Spec.Hmac.hmacBlockKey w.ok.hH.SH.H _ _
  rw [← hu]
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hW := hx.W
  rw [layX_a (by decide)] at hW
  exact hm.bytes (R := ⟨(arg s 4).setWidth 64, w.F.H.D⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [← hW]; exact (hL.kW.sub_left Lay.Ok.fr_stk).symm) (by have := hx.hw.2.2.2.2.2; dsimp only; omega_arith)
    (List.mem_range.mp hi)

end

/-! ## Constant time -/

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The layouts of two calls whose public data agree. -/
theorem layX_eq (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) {N : Nat} {s₁ s₂ : State}
    (hpub : (extractR w f ns N).pub s₁ s₂) : layX w s₂ = layX w s₁ := by
  obtain ⟨hsp, ha, hsy⟩ := hpub
  have hfa : faOf w s₂ = faOf w s₁ := funext fun n => by
    unfold faOf; split
    · next h => exact (hsy n (hns n h)).symm
    · rfl
  have haf : (fun i => if i < 7 then arg s₂ i else 0) = fun i => if i < 7 then arg s₁ i else 0 := funext fun i => by
    split
    · next h => exact (ha i h).symm
    · rfl
  have hA : argAddr s₂ 0 = argAddr s₁ 0 := by simp only [argAddr, hsp]
  simp only [layX, hfa, haf, hA, hsp, ← ha 0 (by decide), ← ha 1 (by decide), ← ha 2 (by decide),
    ← ha 3 (by decide), ← ha 4 (by decide), ← ha 6 (by decide)]

theorem entry_taintX : TaintOk [.esp] (.block (Impl.Hkdf.X86.entry xSh.FB xSh.ti)) := ⟨_, by taint_decide⟩
theorem xtab_taint : TaintOk [.esp, .eax] (.block Impl.Hkdf.X86.extractTab) := ⟨_, by taint_decide⟩
theorem xinitA_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.extractInit) := ⟨_, by taint_decide⟩
theorem xupdA_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.extractUpd) := ⟨_, by taint_decide⟩
theorem xfinA_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.extractFin) := ⟨_, by taint_decide⟩
theorem tblk1_taintX : TaintOk [.esp] (.block [.mov .ebx (Impl.Hkdf.X86.argM xSh.FB xSh.ti)]) := ⟨_, by taint_decide⟩

/-- `esp` and `eax`, the table, agree. -/
theorem agreeEax {K : Hk} {S : Sh} {P : Lay S → Prop} :
    Agree K (fun L _ u => P L ∧ u.gpr .eax = L.tb) [.esp, .eax] := by
  intro L t₁ t₂ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact c₁.esp.trans c₂.esp.symm
  · exact f₁.2.trans f₂.2.symm

/-- Two runs of the frame's body, from calls whose public data agree. -/
theorem extractBody_rel (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) {s₁ s₂ : State}
    (h : (extractR w f ns xStack).pre s₁ ∧ (extractR w f ns xStack).pre s₂ ∧ (extractR w f ns xStack).pub s₁ s₂) :
    RelCT isa (fun a b => a = allocFrame xSh.FB s₁ ∧ b = allocFrame xSh.FB s₂) (Impl.Hkdf.X86.extractBody f)
      fun _ _ => True := by
  obtain ⟨hL, hx⟩ := layX_ok hw h.1
  have he₁ := entryX h.1
  have he₂ := entryX (w := w) h.2.1
  rw [layX_eq hns h.2.2] at he₂
  unfold Impl.Hkdf.X86.extractBody
  refine (start_rel (K := ⟨w, f⟩) hL (P := XOk w) hx he₁ he₂ entry_taintX).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => XOk w L ∧ XBw w L u.mem) (two_prog _ agreeEax xtab_taint)
    fun L g m₀ y t hL hc ⟨hx, ax⟩ => WP.mono (xtab_ok hL hc ax) fun t' ⟨c', hb, _⟩ => ⟨c', hx, hb⟩).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => XOk w L ∧ XBw w L u.mem ∧ XIA L m₀ u) (two_prog [.esp] espOnly xinitA_taint)
    fun L g m₀ y t hL hc ⟨hx, hb⟩ => WP.mono (xinitA_ok hL hc) fun t' ⟨c', ia, hm, _⟩ =>
      ⟨c', hx, by rw [hm]; exact hb, ia⟩).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => XOk w L ∧ XBw w L u.mem) (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintX
    tblk2_taint0 tfn_init (fun _ _ _ _ ⟨hx, hb, a1, a2, a3, a4, a5⟩ hr hm _ => ⟨hx, by rw [hm]; exact hb,
      (hr _ (by decide)).trans a1, (hr _ (by decide)).trans a2, (hr _ (by decide)).trans a3,
      (hr _ (by decide)).trans a4, (hr _ (by decide)).trans a5⟩)
    (init_rel fun L g m₀ y u hL hc ⟨hx, _, ia⟩ => anyX hL hx hc ia))
    fun L g m₀ y t hL hc ⟨hx, hb, ia⟩ => WP.mono (xinit_ok hL hx hc ia hb) fun u ⟨cu, hb', _⟩ =>
      ⟨cu, hx, hb'⟩).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => XOk w L ∧ XBw w L u.mem ∧ XUA w L m₀ u) (two_prog [.esp] espOnly xupdA_taint)
    fun L g m₀ y t hL hc ⟨hx, hb⟩ => WP.mono (xupdA_ok hL hc hb) fun t' ⟨c', ua, hm, _⟩ =>
      ⟨c', hx, by rw [hm]; exact hb, ua⟩).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => XOk w L ∧ XBw w L u.mem) (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintX
    tblk2_taint1 tfn_upd (fun _ _ _ _ ⟨hx, hb, a1, a2, a3, a4, a5, a6⟩ hr hm _ => ⟨hx, by rw [hm]; exact hb,
      (hr _ (by decide)).trans a1, (hr _ (by decide)).trans a2, (hr _ (by decide)).trans a3,
      (hr _ (by decide)).trans a4, (hr _ (by decide)).trans a5, (hr _ (by decide)).trans a6⟩)
    (upd_rel' fun L g m₀ y u hL hc ⟨hx, _, ua⟩ => updX hL hx hc ua))
    fun L g m₀ y t hL hc ⟨hx, hb, ua⟩ => WP.mono (xupd_ok hL hx hc ua hb) fun u ⟨cu, hb', _⟩ =>
      ⟨cu, hx, hb'⟩).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => XOk w L ∧ XFA w L m₀ u) (two_prog [.esp] espOnly xfinA_taint)
    fun L g m₀ y t hL hc ⟨hx, hb⟩ => WP.mono (xfinA_ok hL hc hb) fun t' ⟨c', fa, _⟩ => ⟨c', hx, fa⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintX
    tblk2_taint2 tfn_fin (fun _ _ _ _ ⟨hx, a1, a2, a3, a4, a5, a6⟩ hr _ _ => ⟨hx,
      (hr _ (by decide)).trans a1, (hr _ (by decide)).trans a2, (hr _ (by decide)).trans a3,
      (hr _ (by decide)).trans a4, (hr _ (by decide)).trans a5, (hr _ (by decide)).trans a6⟩)
    (fin_rel fun L g m₀ y u hL hc ⟨hx, fa⟩ => finX hL hx hc fa))
    fun L g m₀ y t hL hc ⟨hx, fa⟩ => WP.mono (xfin_ok hL hx hc fa) fun u ⟨cu, _⟩ => ⟨cu, trivial⟩).seq ?_
  exact two_prog [.esp] espOnly restore_taint

/-- `vg_hkdf_extract` is constant time: two runs whose public data agree have
the same layout, and leak the same trace. -/
theorem extract_ct (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) :
    ConstantTime isa (extractR w f ns xStack).pre (extractR w f ns xStack).pub (Impl.Hkdf.X86.extract f) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.frameAlloc (R := fun _ _ => True)
    ((VG.RelCT.exists_ fun q : State × State => VG.RelCT.exists_ fun h : (extractR w f ns xStack).pre q.1 ∧
      (extractR w f ns xStack).pre q.2 ∧ (extractR w f ns xStack).pub q.1 q.2 => extractBody_rel hw hns h).mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨(s₁, s₂), h, ea, eb⟩) fun _ _ h => h))

end

end VG.Proof.Hkdf.X86
