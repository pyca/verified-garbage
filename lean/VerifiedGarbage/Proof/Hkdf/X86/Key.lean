module

public import VerifiedGarbage.Proof.Hkdf.X86.Env
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Hkdf.X86

/-!
# HKDF on x86 (32-bit): `vg_hkdf_key`, correct and constant time

The contract the proof is written against (`keyR`), for the table `hmac`
of one variant `w` (`HVar`), whose functions an indirect call of `f`'s
reaches: `key(prk, prk_len, key, hmac)` makes the 384 bytes at `key` hold
HMAC's states keyed with `PRK` (`Spec.Hkdf.Keyed`, with `w`'s streaming
states). In its frame (`kFr` bytes: our caller's registers, then the
working space), `keyArgs` moves `init`'s arguments into place (`args_ok`),
HMAC's `init` for a key of any length, through the table, writes the states
(`init_ok`), and the frame's release leaves them as they are
(`key_correct`). The layout of a call (`layK`) is what both of two runs whose
public data agree share; each piece is related in them (`key_ct`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86

open VG VG.X86 VG.X86.Wp
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)
open VG.Proof.HmacTable.X86 (HVar TabOK TabMem)
open VG.Proof.Pbkdf2.Whole.X86.Any (AnyArgs)

/-- What the functions need of a variant: its hash function has HMAC over
its block size, its streaming states fit their 192 bytes, the working space
of its functions the frames', and its digests the 64 bytes of `T(i)`. -/
def HOk (w : HVar) : Prop :=
  (match Spec.HmacTable.hmacOf w.G with
    | some F => F.blockSize = w.F.H.B
    | none => False) ∧
  w.F.H.S ≤ 192 ∧ (w.F.W + w.F.H.S) * 8 ≤ 3408 ∧ w.ok.Wf * 8 ≤ 1872 ∧ w.ok.hH.Wb ≤ 1872 ∧ w.F.H.D ≤ 64

instance (w : HVar) : Decidable (HOk w) := by
  unfold HOk; cases Spec.HmacTable.hmacOf w.G <;> infer_instance

/-- What the contract says of the table: it holds `w`'s HMAC functions,
which an indirect call of `f`'s reaches, then its digest length and HMAC's
block size. -/
def TabFacts (w : HVar) (f : Fns) (s : State) (t : BitVec 32) : Prop :=
  TabOK w.F f s.syms ∧ TabMem w.F s.syms t s.mem ∧
    s.mem.readW (addr t 16) 32 = BitVec.ofNat 32 w.F.H.D ∧
    s.mem.readW (addr t 20) 32 = BitVec.ofNat 32 w.F.H.B

/-- The layout's addresses of the table's functions. -/
def faOf (w : HVar) (s : State) (n : String) : BitVec 32 :=
  if n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN] then s.syms n else 0

/-! ## The contract -/

/-- The stack `vg_hkdf_key` uses: its frame, and the 100 bytes below it the
call of `init` uses. -/
def kStack : Nat := Impl.Hkdf.X86.kFr + 100

/-- `key(prk, prk_len, key, hmac)`, with `N` bytes of stack, for the table
`hmac` of `w`, whose functions an indirect call of `f`'s reaches, with the
addresses of the functions `ns` public. -/
def keyR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let prk : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let key : Region := ⟨(arg s 2).setWidth 64, 384⟩
    let tab : Region := ⟨(arg s 3).setWidth 64, 24⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 N, N⟩
    N ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32 ∧
      s.rd = [prk, tab] ∧ s.wr = [key, args] ∧
      prk.Disjoint key ∧ key.Disjoint tab ∧ key.Disjoint args ∧ ret.Disjoint key ∧
      stk.Disjoint prk ∧ stk.Disjoint key ∧ stk.Disjoint tab ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 24 ≤ 2 ^ 32 ∧ TabFacts w f s (arg s 3)
  post s s' := Spec.Hkdf.Keyed w.ok.hH.SH s'.mem ((arg s 2).setWidth 64)
    (Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 4, arg s₁ i = arg s₂ i) ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-! ## The layout -/

/-- `key`'s frame: 3424 bytes, 100 below it, four arguments, the table the last. -/
def kSh : Sh := ⟨Impl.Hkdf.X86.kFr, 100, 4, 3⟩

/-- The layout of a call from `s`. -/
def layK (w : HVar) (s : State) : Lay kSh where
  E := s.gpr .esp
  a i := if i < 4 then arg s i else 0
  W := ⟨(arg s 2).setWidth 64, 384⟩
  rd := [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨(arg s 3).setWidth 64, 24⟩]
  wr := [⟨(arg s 2).setWidth 64, 384⟩, ⟨argAddr s 0, 16⟩]
  fa := faOf w s

/-- What `key` needs of the layout besides `Lay.Ok`: `PRK`'s place, and the
variant's sizes. -/
structure KOk (w : HVar) (L : Lay kSh) : Prop where
  hw : HOk w
  W : L.W = ⟨(L.a 2).setWidth 64, 384⟩
  pRd : (⟨(L.a 0).setWidth 64, (L.a 1).toNat⟩ : Region) ∈ L.rd
  pW : Region.Disjoint ⟨(L.a 0).setWidth 64, (L.a 1).toNat⟩ L.W
  kP : L.STK.Disjoint ⟨(L.a 0).setWidth 64, (L.a 1).toNat⟩
  np : (L.a 0).toNat + (L.a 1).toNat ≤ 2 ^ 32
  nk : (L.a 2).toNat + 384 ≤ 2 ^ 32

section
variable {w : HVar} {f : Fns} {ns : List String}

theorem kStack_eq : kStack = kSh.N := rfl

theorem argAddr_eq {S : Sh} (L : Lay S) (hL : L.Ok) {s : State} (he : s.gpr .esp = L.E) :
    argAddr s 0 = L.B + BitVec.ofNat 64 (S.N + 4) := by
  have := hL.addrE 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hL.ti)
  simp only [Nat.mul_zero, Nat.add_zero] at this
  rw [← this, ← he]; rfl

theorem B_eq' {S : Sh} {E : BitVec 32} (h : S.N ≤ E.toNat) :
    (E - BitVec.ofNat 32 S.N).setWidth 64 = E.setWidth 64 - BitVec.ofNat 64 S.N := Taint.sub_setWidth h

/-- The layout of a call meeting the contract. -/
theorem layK_ok {s : State} (hw : HOk w) (hp : (keyR w f ns kStack).pre s) : (layK w s).Ok ∧ KOk w (layK w s) := by
  obtain ⟨hsp, htop, hrd, hwr, pk, kt, ka, rk, sp', sk, st, np, nk, nt, -⟩ := hp
  have hB : (layK w s).B = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 kSh.N := B_eq' hsp
  have eK : (layK w s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 kStack, kStack⟩ := by
    show (⟨(layK w s).B, kSh.N⟩ : Region) = _; rw [hB]; rfl
  have eR : (layK w s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show (⟨(layK w s).B + BitVec.ofNat 64 kSh.N, 4⟩ : Region) = _; rw [hB, BitVec.sub_add_cancel]
  have eA : (layK w s).ARGS = ⟨argAddr s 0, 16⟩ := by
    show (⟨(layK w s).B + BitVec.ofNat 64 (kSh.N + 4), 4 * 4⟩ : Region) = _
    rw [hB, ← Offset.add_add ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 kSh.N) kSh.N 4, BitVec.sub_add_cancel]
    show (⟨(s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4, 16⟩ : Region) = ⟨(s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64, 16⟩
    rw [show 4 + 4 * 0 = 4 from rfl, ← addr, addr_eq (by omega_arith)]
  have hT : (layK w s).TAB = ⟨(arg s 3).setWidth 64, 24⟩ := rfl
  have hW : (layK w s).W = ⟨(arg s 2).setWidth 64, 384⟩ := rfl
  refine ⟨⟨hsp, by show (s.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32; omega_arith, by decide, by decide, by decide,
    by decide, by decide, ?_, by rw [eK]; exact sk.symm.symm,
    by rw [eR]; exact rk, by rw [eA]; exact ka.symm, nt, kt.symm, by rw [eK]; exact st.symm, ?_, ?_, ?_⟩,
    ⟨hw, rfl, ?_, pk, by rw [eK]; exact sp', np, nk⟩⟩
  · show (BitVec.setWidth 64 (arg s 2)).toNat + 384 ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; exact nk
  · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  · rw [eA]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  · exact List.mem_cons_self
  · exact List.mem_cons_self

/-- What the contract says on entry, with the layout. -/
theorem entryK {s : State} (hp : (keyR w f ns kStack).pre s) : Entry ⟨w, f⟩ (layK w s) s := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, tok, tm, td, tb⟩ := hp
  exact ⟨rfl, hrd, hwr, fun i hi => by have hi' : i < 4 := hi; simp only [layK, hi', ite_true],
    tok, tm, td, tb, fun n hn => by simp only [layK, faOf, hn, ite_true]⟩

end

/-! ## The frame's body -/

section
variable {w : HVar} {f : Fns} {L : Lay kSh} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32}

/-- What `keyArgs` leaves: `init`'s arguments. -/
def KA : Pr kSh := fun L _ u =>
  u.gpr .edi = L.a 2 ∧ u.gpr .esi = L.a 2 + BitVec.ofNat 32 192 ∧ u.gpr .edx = L.a 0 ∧ u.gpr .ecx = L.a 1 ∧
    u.gpr .ebp = L.F + BitVec.ofNat 32 Impl.Hkdf.X86.kWork

theorem keyArgs_ok (hL : L.Ok) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) :
    WP isa (.block Impl.Hkdf.X86.keyArgs) u fun u' => Ctx ⟨w, f⟩ L g m₀ y u' ∧ KA L m₀ u' ∧ u'.mem = u.mem ∧
      u'.syms = u.syms := by
  rw [Impl.Hkdf.X86.keyArgs, WP.block_append_iff,
    show ([.mov .edi (Impl.Hkdf.X86.argM Impl.Hkdf.X86.kFr 2), .mov .esi (.reg .edi), .alu .add .esi (.imm 192),
      .mov .edx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.kFr 0), .mov .ecx (Impl.Hkdf.X86.argM Impl.Hkdf.X86.kFr 1)] :
        List Instr) = [.mov .edi (Impl.Hkdf.X86.argM kSh.FB 2)] ++ [.mov .esi (.reg .edi)] ++ [.alu .add .esi (.imm 192)] ++
      [.mov .edx (Impl.Hkdf.X86.argM kSh.FB 0)] ++ [.mov .ecx (Impl.Hkdf.X86.argM kSh.FB 1)] from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 2) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (movr_ok hL h₁.ctx (d := .esi) (by decide) .edi) fun u₂ h₂ => ?_
  refine WP.mono (addI_ok hL h₂.ctx (d := .esi) (by decide) 192) fun u₃ h₃ => ?_
  refine WP.mono (arg_ok hL h₃.ctx (d := .edx) (by decide) (i := 0) (by decide)) fun u₄ h₄ => ?_
  refine WP.mono (arg_ok hL h₄.ctx (d := .ecx) (by decide) (i := 1) (by decide)) fun u₅ h₅ => ?_
  refine WP.mono (fr_ok hL h₅.ctx (d := .ebp) (by decide) Impl.Hkdf.X86.kWork) fun u₆ h₆ => ?_
  refine ⟨h₆.ctx, ⟨?_, ?_, ?_, ?_, h₆.val⟩, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [h₆.syms, h₅.syms, h₄.syms, h₃.syms, h₂.syms, h₁.syms]⟩
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide),
      h₂.keep _ (by decide), h₁.val]
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val, h₂.val, h₁.val]; rfl
  · rw [h₆.keep _ (by decide), h₅.keep _ (by decide), h₄.val]
  · rw [h₆.keep _ (by decide), h₅.val]

theorem sx192 : (192 : BitVec 32) = BitVec.ofNat 32 192 := rfl

/-- `init`'s regions, from what `keyArgs` leaves. -/
theorem anyK (hL : L.Ok) (hk : KOk w L) {u : State} (hc : Ctx ⟨w, f⟩ L g m₀ y u) (ha : KA L m₀ u) :
    AnyArgs w.ok.hH.SH (w.F.W + w.F.H.S) u (L.a 2) (L.a 2 + BitVec.ofNat 32 192) (L.a 0)
      (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.kWork) (L.a 1).toNat := by
  obtain ⟨hdi, hsi, hdx, hcx, hbp⟩ := ha
  have hS : w.ok.hH.SH.stateBytes ≤ 192 := by rw [w.ok.hH.hS]; exact hk.hw.2.1
  have hA := hk.hw.2.2.1
  have nB := hL.nB; have := kSh.N_eq; have nk := hk.nk
  have e3 : kSh.FB = 3424 := rfl
  have e4 : kSh.cb = 100 := rfl
  have e5 : kSh.NA = 4 := rfl
  have hk2 : (L.a 2 + BitVec.ofNat 32 192).setWidth 64 = (L.a 2).setWidth 64 + BitVec.ofNat 64 192 :=
    addr_eq (by omega_arith)
  have hsc : (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.kWork).setWidth 64 = L.B + BitVec.ofNat 64 (kSh.cb + 16) :=
    hL.addrF (by decide)
  have hb : Proof.Pbkdf2.Whole.X86.Any.stk100 u = L.CALLS := by
    show below (u.gpr .esp) 100 = _; rw [hc.esp]; exact hL.below_F_eq
  have iW : Region.Sub ⟨(L.a 2).setWidth 64, w.ok.hH.SH.stateBytes⟩ L.W := by
    rw [hk.W]; exact Region.sub_prefix (by omega_arith)
  have oW : Region.Sub ⟨(L.a 2 + BitVec.ofNat 32 192).setWidth 64, w.ok.hH.SH.stateBytes⟩ L.W := by
    rw [hk.W, hk2]; exact Offset.sub_base _ (by omega_arith)
  have sF : Region.Sub ⟨(L.F + BitVec.ofNat 32 Impl.Hkdf.X86.kWork).setWidth 64, (w.F.W + w.F.H.S) * 8⟩ L.HI := by
    rw [hsc]; exact Offset.sub _ (Nat.le_refl _) (by show _ ≤ _ + (3424 - 16); omega_arith)
  have sK := fun x hx => hL.hi_stk x (sF x hx)
  exact
    { edi := hdi, esi := hsi, edx := hdx
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      ebp := hbp
      kl32 := (L.a 1).isLt
      sp := by rw [hc.esp, hL.FN]; have := hL.e0; omega_arith
      cr := VG.Covers.left (by
        rw [hc.rd]; exact VG.Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hk.pRd)
      cw := by
        rw [hc.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.W, List.mem_cons_of_mem _ hL.wWr, 0, by rw [hk.W]; exact (BitVec.add_zero _).symm,
            by rw [hk.W]; dsimp only; omega_arith⟩
        · exact ⟨L.W, List.mem_cons_of_mem _ hL.wWr, 192, by rw [hk.W]; exact hk2,
            by rw [hk.W]; dsimp only; omega_arith⟩
        · exact ⟨L.FR, List.mem_cons_self, 16, by rw [hsc]; exact (Offset.add_add _ _ _).symm,
            by dsimp only; omega_arith⟩
      i_o := by
        rw [hk2]
        have := Offset.base_disjoint ((L.a 2).setWidth 64) (e := 192) (n := w.ok.hH.SH.stateBytes)
          (k := w.ok.hH.SH.stateBytes) hS (by omega_arith)
        exact this
      i_k := (hk.pW.sub_right iW).symm
      i_s := (hL.kW.sub_left sK).symm.sub_left iW
      o_k := (hk.pW.sub_right oW).symm
      o_s := (hL.kW.sub_left sK).symm.sub_left oW
      k_s := (hk.kP.sub_left sK).symm
      b_i := by rw [hb]; exact hL.calls_W.sub_right iW
      b_o := by rw [hb]; exact hL.calls_W.sub_right oW
      b_k := by rw [hb]; exact hk.kP.sub_left Lay.Ok.calls_stk
      b_s := by
        rw [hb]
        exact (Offset.base_disjoint L.B (e := kSh.cb + 16) (n := (w.F.W + w.F.H.S) * 8) (k := kSh.cb)
          (by omega_arith) (by omega_arith)).sub_right
          (by rw [hsc]; exact fun x hx => hx)
      ni := by omega_arith
      no := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 192) (by omega_arith),
          Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      nk := hk.np
      nsc := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Impl.Hkdf.X86.kWork) (by decide), hL.FN,
          Nat.mod_eq_of_lt (by have := hL.e1; have := hL.e0; show L.E.toNat - 3424 + 16 < _; omega_arith)]
        have := hL.e1; have := hL.e0; show L.E.toNat - 3424 + 16 + _ ≤ _; omega_arith }

end

/-! ## Correct -/

section
variable {w : HVar} {f : Fns} {ns : List String}

theorem layK_a {s : State} {i : Nat} (hi : i < 4) : (layK w s).a i = arg s i := by
  simp only [layK, hi, ite_true]

/-- `init`'s call through the table, from what `keyArgs` leaves. -/
theorem kinit_ok {L : Lay kSh} {g : Reg → BitVec 32} {m₀ : Mem} {y : String → BitVec 32} (hL : L.Ok) (hk : KOk w L)
    {t : State} (hc : Ctx ⟨w, f⟩ L g m₀ y t) (ka : KA L m₀ t) :
    WP isa (Impl.Hkdf.X86.tcall Impl.Hkdf.X86.kFr 3 0 f.init Impl.Ecdsa.Rfc6979.X86.init5) t fun u =>
      Ctx ⟨w, f⟩ L g m₀ y u ∧ u.mem = u.mem ∧
      w.ok.hH.SH.Repr u.mem ((L.a 2).setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey w.ok.hH.SH.H
          (Spec.Sha256.bytesAt t.mem ((L.a 0).setWidth 64) (L.a 1).toNat)) Spec.Hmac.ipad) ∧
      w.ok.hH.SH.Repr u.mem ((L.a 2 + BitVec.ofNat 32 192).setWidth 64)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey w.ok.hH.SH.H
          (Spec.Sha256.bytesAt t.mem ((L.a 0).setWidth 64) (L.a 1).toNat)) Spec.Hmac.opad) := by
  refine tcall_ok (K := ⟨w, f⟩) hL hc (j := 0) (by decide) (by rw [Nat.mul_zero]; exact hc.tabMem.1) hc.tabOk.i
    fun t' c' hm' hk' _ => ?_
  have ka' : KA L m₀ t' := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := ka
    exact ⟨(hk' _ (by decide)).trans a1, (hk' _ (by decide)).trans a2, (hk' _ (by decide)).trans a3,
      (hk' _ (by decide)).trans a4, (hk' _ (by decide)).trans a5⟩
  have hS : w.ok.hH.SH.stateBytes ≤ 192 := by rw [w.ok.hH.hS]; exact hk.hw.2.1
  have hA := hk.hw.2.2.1
  have nk := hk.nk; have nB := hL.nB; have := kSh.N_eq
  have e3 : kSh.FB = 3424 := rfl
  have e4 : kSh.cb = 100 := rfl
  have hk2 : (L.a 2 + BitVec.ofNat 32 192).setWidth 64 = (L.a 2).setWidth 64 + BitVec.ofNat 64 192 :=
    addr_eq (by omega_arith)
  refine WP.mono (init_wp hL c' (anyK hL hk c' ka') (by decide) fun r hr => ?_) fun u ⟨cu, _, _, hi, ho⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (by rw [hk.W]; exact Region.sub_prefix (by omega_arith))
    · exact .inl (by rw [hk.W, hk2]; exact Offset.sub_base _ (by omega_arith))
    · refine .inr (.inl ?_)
      rw [show (L.F + BitVec.ofNat 32 Impl.Hkdf.X86.kWork).setWidth 64 = L.B + BitVec.ofNat 64 (kSh.cb + 16) from
        hL.addrF (by decide)]
      exact Offset.sub _ (Nat.le_refl _) (by show _ ≤ _ + (kSh.FB - 16); omega_arith)
  · rw [hm'] at hi ho
    exact ⟨cu, rfl, hi, ho⟩

/-- The frame's body of `vg_hkdf_key`. -/
theorem keyBody_ok {s : State} (hL : (layK w s).Ok) (hk : KOk w (layK w s)) (he : Entry ⟨w, f⟩ (layK w s) s) :
    WP isa (Impl.Hkdf.X86.keyBody f) (allocFrame kSh.FB s) fun u => Ctx ⟨w, f⟩ (layK w s) s.gpr s.mem s.syms u ∧
      (∀ p ∈ Impl.Hkdf.X86.saved, u.gpr p.1 = s.gpr p.1) ∧
      Spec.Hkdf.Keyed w.ok.hH.SH u.mem ((arg s 2).setWidth 64)
        (Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  unfold Impl.Hkdf.X86.keyBody
  refine WP.seq (WP.mono (entry_ok hL he) fun t₁ ⟨c₁, _⟩ => ?_)
  refine WP.seq (WP.mono (keyArgs_ok hL c₁) fun t₂ ⟨c₂, ka, hm₂, _⟩ => ?_)
  refine WP.seq (WP.mono (kinit_ok hL hk c₂ ka) fun u ⟨cu, _, hi, ho⟩ => ?_)
  refine WP.mono (restore_ok hL cu) fun u' ⟨cu', hr, hm⟩ => ⟨cu', hr, ?_⟩
  have hbP : Spec.Sha256.bytesAt t₂.mem ((arg s 0).setWidth 64) (arg s 1).toNat =
      Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat := by
    simp only [Spec.Sha256.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := c₂.bytes (R := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩) hk.pW hk.kP.symm
      (by show (arg s 1).toNat ≤ 2 ^ 64; have := (arg s 1).isLt; omega_arith) (List.mem_range.mp hi)
    exact this
  rw [layK_a (by decide), layK_a (by decide), layK_a (by decide), hbP] at hi ho
  have nk := hk.nk
  rw [hm]
  refine ⟨hi, ?_⟩
  rw [← addr_eq (x := arg s 2) (k := 192) (by rw [layK_a (by decide)] at nk; omega_arith)]
  exact ho

/-- `vg_hkdf_key`: its frame, the arguments, and HMAC's `init` through the table. -/
theorem key_correct {s : State} (hw : HOk w) (hsp : NoSp (Impl.Hkdf.X86.keyBody f))
    (hp : (keyR w f ns kStack).pre s) :
    WP isa (Impl.Hkdf.X86.key f) s fun s' => abiPreserved s s' ∧ (keyR w f ns kStack).post s s' := by
  obtain ⟨hL, hk⟩ := layK_ok hw hp
  have he := entryK hp
  refine WP.mono (frame_ok hL he hsp (keyBody_ok hL hk he)) fun s' ⟨ha, u, ⟨hi, ho⟩, hm⟩ => ⟨ha, ?_, ?_⟩
  all_goals
    have hS : w.ok.hH.SH.stateBytes ≤ 192 := by rw [w.ok.hH.hS]; exact hk.hw.2.1
    have nk := hk.nk; rw [layK_a (by decide)] at nk
  · refine w.ok.hH.repr _ _ _ _ _ (fun i hi' => ?_) hi
    refine hm.bytes (R := ⟨(arg s 2).setWidth 64, 384⟩) (fun r hr => ?_) (by dsimp only; omega_arith) (by
      rw [w.ok.hH.hS] at hS; dsimp only; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact (hL.kW.sub_left Lay.Ok.fr_stk).symm
  · refine w.ok.hH.repr _ _ _ _ _ (fun i hi' => ?_) ho
    have e := hm.bytes (R := ⟨(arg s 2).setWidth 64 + BitVec.ofNat 64 192, 192⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.kW.sub_left Lay.Ok.fr_stk).sub_right (Offset.sub_base _ (by omega_arith))).symm)
      (by dsimp only; omega_arith) (i := i) (by rw [w.ok.hH.hS] at hS; dsimp only; omega_arith)
    exact e

end

/-! ## Constant time -/

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The layouts of two calls whose public data agree. -/
theorem layK_eq (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) {N : Nat} {s₁ s₂ : State}
    (hpub : (keyR w f ns N).pub s₁ s₂) : layK w s₂ = layK w s₁ := by
  obtain ⟨hsp, ha, hsy⟩ := hpub
  have hfa : faOf w s₂ = faOf w s₁ := funext fun n => by
    unfold faOf; split
    · next h => exact (hsy n (hns n h)).symm
    · rfl
  have haf : (fun i => if i < 4 then arg s₂ i else 0) = fun i => if i < 4 then arg s₁ i else 0 := funext fun i => by
    split
    · next h => exact (ha i h).symm
    · rfl
  have hA : argAddr s₂ 0 = argAddr s₁ 0 := by simp only [argAddr, hsp]
  simp only [layK, hfa, haf, hA, hsp, ← ha 0 (by decide), ← ha 1 (by decide), ← ha 2 (by decide), ← ha 3 (by decide)]

theorem entry_taintK : TaintOk [.esp] (.block (Impl.Hkdf.X86.entry kSh.FB kSh.ti)) := ⟨_, by taint_decide⟩
theorem keyArgs_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.keyArgs) := ⟨_, by taint_decide⟩
theorem tblk1_taintK : TaintOk [.esp] (.block [.mov .ebx (Impl.Hkdf.X86.argM kSh.FB kSh.ti)]) := ⟨_, by taint_decide⟩
theorem restore_taint : TaintOk [.esp] (.block Impl.Hkdf.X86.restoreRegs) := ⟨_, by taint_decide⟩

theorem keepsB_ka : KeepsB (fun L m₀ u => KOk w L ∧ KA L m₀ u) := fun _ _ _ _ ⟨hk, a1, a2, a3, a4, a5⟩ hr _ _ =>
  ⟨hk, (hr _ (by decide)).trans a1, (hr _ (by decide)).trans a2, (hr _ (by decide)).trans a3,
    (hr _ (by decide)).trans a4, (hr _ (by decide)).trans a5⟩

/-- Two runs of the frame's body, from calls whose public data agree. -/
theorem keyBody_rel (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) {s₁ s₂ : State}
    (h : (keyR w f ns kStack).pre s₁ ∧ (keyR w f ns kStack).pre s₂ ∧ (keyR w f ns kStack).pub s₁ s₂) :
    RelCT isa (fun a b => a = allocFrame kSh.FB s₁ ∧ b = allocFrame kSh.FB s₂) (Impl.Hkdf.X86.keyBody f)
      fun _ _ => True := by
  obtain ⟨hL, hk⟩ := layK_ok hw h.1
  have he₁ := entryK h.1
  have he₂ := entryK (w := w) h.2.1
  rw [layK_eq hns h.2.2] at he₂
  unfold Impl.Hkdf.X86.keyBody
  refine (start_rel (K := ⟨w, f⟩) hL (P := KOk w) hk he₁ he₂ entry_taintK).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => KOk w L ∧ KA L m₀ u) (two_prog [.esp] espOnly keyArgs_taint)
    fun L g m₀ y t hL hc ⟨hk, _⟩ => WP.mono (keyArgs_ok hL hc) fun t' ⟨c', ka, _⟩ => ⟨c', hk, ka⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (tcall_rel (K := ⟨w, f⟩) (by decide) tblk1_taintK tblk2_taint0 tfn_init
    keepsB_ka (init_rel fun L g m₀ y u hL hc ⟨hk, ka⟩ => anyK hL hk hc ka))
    fun L g m₀ y t hL hc ⟨hk, ka⟩ => WP.mono (kinit_ok hL hk hc ka) fun u ⟨cu, _⟩ => ⟨cu, trivial⟩).seq ?_
  exact two_prog [.esp] espOnly restore_taint

/-- `vg_hkdf_key` is constant time: two runs whose public data agree have the
same layout, and leak the same trace. -/
theorem key_ct (hw : HOk w) (hns : ∀ n ∈ [w.F.hiAnyN, w.F.H.updN, w.F.hfN], n ∈ ns) :
    ConstantTime isa (keyR w f ns kStack).pre (keyR w f ns kStack).pub (Impl.Hkdf.X86.key f) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.frameAlloc (R := fun _ _ => True)
    ((VG.RelCT.exists_ fun q : State × State => VG.RelCT.exists_ fun h : (keyR w f ns kStack).pre q.1 ∧
      (keyR w f ns kStack).pre q.2 ∧ (keyR w f ns kStack).pub q.1 q.2 => keyBody_rel hw hns h).mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨(s₁, s₂), h, ea, eb⟩) fun _ _ h => h))

end

end VG.Proof.Hkdf.X86
