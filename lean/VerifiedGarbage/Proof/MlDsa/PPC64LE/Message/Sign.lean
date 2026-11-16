module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Pieces
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Pieces
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Base
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `MlDsa.PPC64LE.Message.Steps`, which only this module used -/

section

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message_cached`: the steps

As Ed448's whole functions on this target (`Proof/Ed448/PPC64LE/Whole/`),
whose invariant `Inv` (`Proof/Ed25519/PPC64LE/Whole/Frame.lean`) they share:
the registers `rs` and the link register saved at `oSV(E)`, then the
arguments moved into `rs` (`setup_ok`, by `movs_ok`); the two bytes
`0 ‖ ctx_len` stored at `oHdr(E)` (`hdr_ok`); a hash, or any step that keeps
the callee-saved registers and writes within the body's regions, apart from
the slots, keeps `Inv` (`inv_kept`); the branch on `ctx_len >> 8`
(`wp_ite`, `shr8_zero`); and the moves of a call's arguments (`args4_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Impl.Ed25519.PPC64LE.Whole (saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea save_ok saveG)
open VG.Impl.Sha3.PPC64LE.Pieces (Piece Len)
open VG.Proof.Sha3.PPC64LE.Pieces (Kept PieceOk)

/-- `mov`s from registers that none of them writes, to distinct registers. -/
theorem movs_ok : ∀ (ms : List (Reg × Reg)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ p ∈ ms, p.2 ≠ .r0 ∧ p.2 ∉ ms.map Prod.fst) → (ms.map Prod.fst).Nodup →
    (∀ u, u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      (∀ p ∈ ms, u.gpr p.1 = s.gpr p.2) → (∀ r, r ∉ ms.map Prod.fst → u.gpr r = s.gpr r) →
      WP isa (.block rest) u Q) →
    WP isa (.block (ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  intro ms
  induction ms with
  | nil => exact fun _ _ k => k _ rfl rfl rfl rfl (fun _ h => absurd h List.not_mem_nil) fun _ _ => rfl
  | cons p ms ih =>
    intro s rest Q hs hn k
    obtain ⟨d, n⟩ := p
    obtain hn' := List.nodup_cons.mp hn
    obtain h0 := hs (d, n) List.mem_cons_self
    simp only [List.map_cons, List.cons_append]
    refine wp_addi h0.1 (by decide) fun u hu => ih (fun q hq => ⟨(hs q (List.mem_cons_of_mem _ hq)).1,
      fun h => (hs q (List.mem_cons_of_mem _ hq)).2 (List.mem_cons_of_mem _ h)⟩) hn'.2
      fun u' m' rd' wr' sp' hm ho => k u' (m'.trans hu.mem) (rd'.trans hu.rd) (wr'.trans hu.wr) (sp'.trans hu.sp)
        (fun q hq => ?_) fun r hr => ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hn'.1, hu.gpr, BitVec.add_zero]
      · have hq2 : q.2 ≠ d := fun e => (hs q (List.mem_cons_of_mem _ hq)).2 (e ▸ List.mem_cons_self)
        rw [hm q hq, hu.other _ hq2]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, hu.other r hr.1]

/-- The saves at `o(F)` (`F` in `f`), then the moves `ms` into the registers `rs`, which hold `v`: the
invariant holds after them. -/
theorem setup_ok {s : State} {f : Reg} {o : Nat} {rs : List Reg} {ms : List (Reg × Reg)} {v : Reg → BitVec 64}
    {W : List Region} {rest : List Instr} {Q : State → Prop} (hf0 : f ≠ .r0)
    (hfits : Spill.Fits (slots o rs)) (hlo : o + 8 * (rs.length + 1) < 2 ^ 64)
    (hin : ∀ p ∈ slots o rs, InRegions s.wr (s.gpr f + BitVec.ofNat 64 p.2) 8)
    (hW : ∃ R ∈ W, Region.Sub (slotArea (s.gpr f) o rs) R) (hms : ms.map Prod.fst = rs)
    (hsrc : ∀ p ∈ ms, p.2 ≠ .r0 ∧ p.2 ∉ rs) (hnd : rs.Nodup) (hv : ∀ p ∈ ms, v p.1 = s.gpr p.2)
    (k : ∀ u, Inv s (s.gpr f) o rs v W u → WP isa (.block rest) u Q) :
    WP isa (.block (saveRegs f o rs ++ ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  rw [List.append_assoc]
  refine save_ok hf0 hfits hlo hin fun u hu _ hsv hfr => ?_
  refine movs_ok ms (fun p hp => ⟨(hsrc p hp).1, hms ▸ (hsrc p hp).2⟩) (hms ▸ hnd)
    fun u' m' rd' wr' sp' hm ho => k u' ⟨rd'.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, fun r hr => ?_,
      fun r hr hn => ?_, m' ▸ hsv, m' ▸ hfr.sub fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hW⟩
  · rw [← hms] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    rw [hm p hp, hv p hp, hu.gpr _ (by simpa using (hsrc p hp).1)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simpa using fun e => (by revert hr; rw [e]; decide : False))]

/-- A step that keeps the callee-saved registers, writing within `W` and apart from the slots. -/
theorem inv_kept {s t t' : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W Wc : List Region}
    (h : Inv s F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hk : Kept Wc t t')
    (hsub : ∀ r ∈ Wc, ∃ R ∈ W, Region.Sub r R) (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea F o rs) r) :
    Inv s F o rs v W t' :=
  h.step hrs hk.rd hk.wr hk.sp hk.cs hk.frame hsub hd

/-- `Inv` from a state that agrees with `s` on what it records. -/
theorem inv_rebase {s u t : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W : List Region}
    (h : Inv u F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.lr = s.lr) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hm : u.mem = s.mem) :
    Inv s F o rs v W t where
  rd := h.rd.trans hrd
  wr := h.wr.trans hwr
  sp := h.sp.trans hsp
  regs := h.regs
  pres r hr hn := (h.pres r hr hn).trans (hg r hr)
  saved p hp := by
    rw [h.saved p hp]
    obtain ⟨⟨r, i⟩, hm', rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, hlt, he⟩ := List.mem_zipIdx hm'
    obtain hm'' : r ∈ rs ++ [.r0] := by rw [he]; exact List.getElem_mem _
    simp only [saveG]
    by_cases h0 : r = .r0
    · simp only [h0, ↓reduceIte, hlr]
    · have hr : r ∈ rs := by
        rcases List.mem_append.mp hm'' with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') h0
      simp only [h0, ↓reduceIte, hg r (hrs r hr)]
  frame := hm ▸ h.frame

/-! ## Pieces and regions -/

theorem pieceOk_of {N : Nat} {t : State} {sc : Addr} {p : Piece} {R : Region} (hR : p.R t.gpr = R)
    (hb : p.base ∈ preserved) (ho : p.off < 2 ^ 15) (hl : p.len.Ok) (hc : PPC64LE.Covers [R] (t.rd ++ t.wr))
    (hd : R.Disjoint ⟨sc, N⟩) (hb' : (below t.sp 48).Disjoint R) : PieceOk N sc t p :=
  ⟨hb, ho, hl, hR ▸ hc, hR ▸ hd, hR ▸ hb'⟩

theorem cov_in {ws : List Region} {P : Addr} {k d n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : d + n ≤ k) :
    PPC64LE.Covers [⟨P + BitVec.ofNat 64 d, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, d, rfl, h⟩

theorem cov_in0 {ws : List Region} {P : Addr} {k n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : n ≤ k) :
    PPC64LE.Covers [⟨P, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, 0, by simp, by simpa using h⟩

theorem cov_rd {rd wr ws : List Region} (h : PPC64LE.Covers ws rd) : PPC64LE.Covers ws (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_left _ hr, hc⟩

/-! ## The header -/

/-- The memory after the two bytes `0 ‖ c` at `a`. -/
abbrev hdrMem (m : Mem) (a : Addr) (c : BitVec 64) : Mem :=
  (m.writeW a ((0 : BitVec 64).setWidth 8)).writeW (a + BitVec.ofNat 64 1) (c.setWidth 8)

theorem hdrMem_bytes (m : Mem) (a : Addr) (c : Nat) :
    Spec.Sha3.bytesAt (hdrMem m a (BitVec.ofNat 64 c)) a 2 = [0, BitVec.ofNat 8 c] := by
  obtain hne : a ≠ a + BitVec.ofNat 64 1 := fun e => by
    have := congrArg (fun x => (x - a).toNat) e
    simp only [BitVec.sub_self, Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  simp only [Spec.Sha3.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil,
    show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a, hdrMem]
  rw [Proof.MlDsa.Message.byte_writeW_self, Proof.MlDsa.Message.byte_writeW_other _ hne,
    Proof.MlDsa.Message.byte_writeW_self]
  simp only [List.cons.injEq, and_true]
  refine ⟨rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem hdrMem_frame (m : Mem) (a : Addr) (c : BitVec 64) : Frame [⟨a, 2⟩] m (hdrMem m a c) := by
  refine Frame.write (Frame.write (Frame.refl _ _) List.mem_cons_self _ ?_) List.mem_cons_self _ ?_
  · simpa using Offset.contains_base a (d := 0) (n := 1) (k := 2) (by decide) (by decide)
  · exact Offset.contains_base a (d := 1) (n := 1) (k := 2) (by decide) (by decide)

/-- `0 ‖ c` at `o(f)` (`c` in `cr`). -/
theorem hdr_ok {s : State} {f cr : Reg} (hf0 : f ≠ .r0) (hc0 : cr ≠ .r0) {o : Nat} (ho : o + 1 < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr f + BitVec.ofNat 64 o) 1) (hw1 : InRegions s.wr (s.gpr f + BitVec.ofNat 64 (o + 1)) 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.mem = hdrMem s.mem (s.gpr f + BitVec.ofNat 64 o) (s.gpr cr) → t.rd = s.rd → t.wr = s.wr →
      t.sp = s.sp → (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (([.li .r0 0, .stb .r0 f o, .stb cr f (o + 1)] : List Instr) ++ is)) s Q := by
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun u₁ h₁ => ?_
  obtain g : u₁.gpr f = s.gpr f := h₁.other _ hf0
  refine wp_stb hf0 (by omega_using [ho]) rfl (by rw [h₁.wr, g]; exact hw) fun u₂ h₂ => ?_
  refine wp_stb hf0 ho rfl (by rw [h₂.wr, h₁.wr, h₂.gpr, g]; exact hw1) fun u₃ h₃ => ?_
  refine k u₃ ?_ (by rw [h₃.rd, h₂.rd, h₁.rd]) (by rw [h₃.wr, h₂.wr, h₁.wr]) (by rw [h₃.sp, h₂.sp, h₁.sp])
    fun r hr => by rw [h₃.gpr, h₂.gpr, h₁.other _ hr]
  rw [h₃.mem, h₂.gpr, h₂.mem, h₁.mem, g, h₁.gpr, h₁.other _ hc0, hdrMem, Proof.MlDsa.Message.add_add]
  rfl

/-! ## The branch on the length of the context -/

theorem wp_ite {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, s', Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, s', Exec.iteT hc e, q⟩

theorem shr8_zero (x : BitVec 64) : (x >>> 8 == 0#64) = decide (x.toNat < 256) := by
  obtain h : (x >>> 8).toNat = x.toNat / 256 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : x.toNat < 256
  · simp only [hx, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [h, Nat.div_eq_of_lt hx]; rfl)
  · simp only [hx, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [h] at this
    exact hx (by simp at this; omega_using [this])

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0#64) := by
  simp [eval, State.read, Size.bits]

end VG.Proof.MlDsa.PPC64LE.Message

end

end

/-! ### `MlDsa.PPC64LE.Message.Contracts`, which only this module used -/

section

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message_cached`: the contracts, evaluated

The preconditions of `signMessageContract` and `verifyMessageCachedContract`,
and of their versions with prepared keys (`pr`: `preparedSignMessageContract`,
`preparedVerifyMessageContract`, `msgSK`, `msgVK`), by register (`MSPre`,
`MCPre`, which extends `MVPre`): the key is the region of `kLS p pr` or
`kLV p pr` bytes at `r3`, a prepared key with `pr`. And the contracts of the
functions on `μ` they call, `vg_mldsa*_sign` and `vg_mldsa*_verify`, or
`vg_mldsa*_sign_prepared` and `vg_mldsa*_verify_prepared` (`signK`,
`verifyK`): what their preconditions need (`sign_pre`, `verify_pre`), what
their postconditions give (`sign_post`, `verify_post`), and their public
parts (`sign_pub`, `verify_pub`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Ordinary and prepared keys -/

/-- The length of a private key: encoded, or prepared (`pr`). -/
abbrev kLS (p : Params) (pr : Bool) : Nat := if pr then preparedSecretKeyBytes p else p.skLen
/-- The length of a public key: encoded, or prepared (`pr`). -/
abbrev kLV (p : Params) (pr : Bool) : Nat := if pr then preparedPublicKeyBytes p else p.pkLen

/-- The contract of `sign_message`, or of `sign_message_prepared`. -/
def msgSK (p : Params) (pr : Bool) (A : Abi isa) (stk : Nat) : Contract isa :=
  if pr then preparedSignMessageContract p A stk else signMessageContract p A stk
/-- The contract of `verify_message_cached`, or of `verify_message_prepared`. -/
def msgVK (p : Params) (pr : Bool) (A : Abi isa) (stk : Nat) : Contract isa :=
  if pr then preparedVerifyMessageContract p A stk else verifyMessageCachedContract p A stk
/-- The contract of the signing function on `μ` they call. -/
def signK (p : Params) (pr : Bool) (A : Abi isa) (stk : Nat) : Contract isa :=
  if pr then Proof.MlDsa.preparedSignContract p A stk else signContract p A stk
/-- The contract of the verification function on `μ` they call. -/
def verifyK (p : Params) (pr : Bool) (A : Abi isa) (stk : Nat) : Contract isa :=
  if pr then Proof.MlDsa.preparedVerifyContract p A stk else verifyContract p A stk

/-! ## `sign_message` -/

section
variable (p : Params) (pr : Bool) (s : State)

/-- `sk`, `msg`, `ctx`, `rnd`, `sig` and `scratch`. -/
abbrev skR : Region := ⟨s.gpr .r3, kLS p pr⟩
abbrev msgR : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
abbrev ctxR : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev rndR : Region := ⟨s.gpr .r8, 32⟩
abbrev sigR : Region := ⟨s.gpr .r9, p.sigLen⟩
abbrev scrR : Region := ⟨s.gpr .r10, messageScratchWords p * 8⟩

end

/-- `msgSK`'s precondition, by register. -/
structure MSPre (p : Params) (pr : Bool) (STK : Nat) (s : State) : Prop where
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [skR p pr s, msgR s, ctxR s, rndR s]
  wr : s.wr = [sigR p s, scrR p s]
  kg : (skR p pr s).Disjoint (sigR p s)
  kc : (skR p pr s).Disjoint (scrR p s)
  mg : (msgR s).Disjoint (sigR p s)
  mc : (msgR s).Disjoint (scrR p s)
  cg : (ctxR s).Disjoint (sigR p s)
  cc : (ctxR s).Disjoint (scrR p s)
  rg : (rndR s).Disjoint (sigR p s)
  rc : (rndR s).Disjoint (scrR p s)
  gc : (sigR p s).Disjoint (scrR p s)
  bk : (below s.sp STK).Disjoint (skR p pr s)
  bm : (below s.sp STK).Disjoint (msgR s)
  bc : (below s.sp STK).Disjoint (ctxR s)
  br : (below s.sp STK).Disjoint (rndR s)
  bg : (below s.sp STK).Disjoint (sigR p s)
  bx : (below s.sp STK).Disjoint (scrR p s)
  fk : (s.gpr .r3).toNat + kLS p pr ≤ 2 ^ 64
  fm : (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  fc : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  fr : (s.gpr .r8).toNat + 32 ≤ 2 ^ 64
  fg : (s.gpr .r9).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .r10).toNat + messageScratchWords p * 8 ≤ 2 ^ 64
  x : pr = true → PreparedSecretKey p s.mem (s.gpr .r3)

/-- The encoded key, the first bytes of the key's region. -/
theorem MSPre.subK {p : Params} {pr : Bool} {STK : Nat} {s : State} (h : MSPre p pr STK s) :
    Region.Sub ⟨s.gpr .r3, p.skLen⟩ (skR p pr s) := fun a ha => by
  have := h.fk
  cases pr <;> simp only [kLS, Bool.false_eq_true, ↓reduceIte, Region.Contains] at ha this ⊢
  · exact ha
  · simp only [preparedSecretKeyBytes] at this ⊢; omega_using [ha]

theorem mspre_of {p : Params} {pr : Bool} {n : Nat} {s : State}
    (h : (msgSK p pr PPC64LE.abi (n + 1)).pre s) : MSPre p pr (n + 1) s := by
  cases pr
  · simp only [msgSK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pre [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, nofun⟩
  · simp only [msgSK, ↓reduceIte] at h
    sig_pre [preparedSignMessageContract, preparedSignMessageSig, PPC64LE.abi, PPC64LE.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, fun _ => h24⟩

/-! ## `verify_message_cached` -/

section
variable (p : Params) (pr : Bool) (s : State)

/-- `pk`, `sig` and `scratch` (`msg` and `ctx` as signing's). -/
abbrev pkR : Region := ⟨s.gpr .r3, kLV p pr⟩
abbrev vsigR : Region := ⟨s.gpr .r8, p.sigLen⟩
abbrev vscrR : Region := ⟨s.gpr .r9, messageScratchWords p * 8⟩

end

/-- `msgVK`'s precondition, by register, but for `tr`. -/
structure MVPre (p : Params) (pr : Bool) (STK : Nat) (s : State) : Prop where
  stk : STK ≤ s.sp.toNat
  rd : ∀ R ∈ [pkR p pr s, msgR s, ctxR s, vsigR p s], R ∈ s.rd
  wr : s.wr = [vscrR p s]
  kc : (pkR p pr s).Disjoint (vscrR p s)
  mc : (msgR s).Disjoint (vscrR p s)
  cc : (ctxR s).Disjoint (vscrR p s)
  gc : (vsigR p s).Disjoint (vscrR p s)
  bk : (below s.sp STK).Disjoint (pkR p pr s)
  bm : (below s.sp STK).Disjoint (msgR s)
  bc : (below s.sp STK).Disjoint (ctxR s)
  bg : (below s.sp STK).Disjoint (vsigR p s)
  bx : (below s.sp STK).Disjoint (vscrR p s)
  fk : (s.gpr .r3).toNat + kLV p pr ≤ 2 ^ 64
  fm : (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  fc : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  fg : (s.gpr .r8).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .r9).toNat + messageScratchWords p * 8 ≤ 2 ^ 64

/-- The cached `tr`. -/
abbrev trR (s : State) : Region := ⟨s.gpr .r10, 64⟩

/-- `msgVK`'s precondition, by register: `MVPre`, and `tr`. -/
structure MCPre (p : Params) (pr : Bool) (STK : Nat) (s : State) : Prop extends MVPre p pr STK s where
  rdt : trR s ∈ s.rd
  ct : (vscrR p s).Disjoint (trR s)
  bt : (below s.sp STK).Disjoint (trR s)
  ft : (s.gpr .r10).toNat + 64 ≤ 2 ^ 64
  tr : bytesAt s.mem (s.gpr .r10) 64 = pkTr (bytesAt s.mem (s.gpr .r3) p.pkLen)
  x : pr = true → PreparedPublicKey p s.mem (s.gpr .r3)

/-- The encoded key, the first bytes of the key's region. -/
theorem MVPre.subK {p : Params} {pr : Bool} {STK : Nat} {s : State} (h : MVPre p pr STK s) :
    Region.Sub ⟨s.gpr .r3, p.pkLen⟩ (pkR p pr s) := fun a ha => by
  have := h.fk
  cases pr <;> simp only [kLV, Bool.false_eq_true, ↓reduceIte, Region.Contains] at ha this ⊢
  · exact ha
  · simp only [preparedPublicKeyBytes] at this ⊢; omega_using [ha]

theorem mcpre_of {p : Params} {pr : Bool} {n : Nat} {s : State}
    (h : (msgVK p pr PPC64LE.abi (n + 1)).pre s) : MCPre p pr (n + 1) s := by
  cases pr
  · simp only [msgVK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, PPC64LE.abi, PPC64LE.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
    exact ⟨⟨h0, fun R hR => (by rw [h1]; exact List.mem_append_left [trR s] hR), h2, h3, h4, h5, h6, h8, h9, h10,
      h11, h12, h14, h15, h16, h17, h18⟩,
      (by rw [h1]; exact List.mem_append_right [pkR p false s, msgR s, ctxR s, vsigR p s] List.mem_cons_self), h7,
      h13, h19, h20, nofun⟩
  · simp only [msgVK, ↓reduceIte] at h
    sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, PPC64LE.abi, PPC64LE.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ :=
      h
    exact ⟨⟨h0, fun R hR => (by rw [h1]; exact List.mem_append_left [trR s] hR), h2, h3, h4, h5, h6, h8, h9, h10,
      h11, h12, h14, h15, h16, h17, h18⟩,
      (by rw [h1]; exact List.mem_append_right [pkR p true s, msgR s, ctxR s, vsigR p s] List.mem_cons_self), h7,
      h13, h19, h21, fun _ => h20⟩

/-! ## The functions on `μ` -/

section
variable {p : Params} {stk : Nat} {x y : State}

theorem sign_pre {pr : Bool} {k m r g c : Addr} (g3 : x.gpr .r3 = k) (g4 : x.gpr .r4 = m) (g5 : x.gpr .r5 = r)
    (g6 : x.gpr .r6 = g) (g7 : x.gpr .r7 = c)
    (hrd : x.rd = [⟨k, kLS p pr⟩, ⟨m, 64⟩, ⟨r, 32⟩]) (hwr : x.wr = [⟨g, p.sigLen⟩, ⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat)
    (d1 : Region.Disjoint ⟨k, kLS p pr⟩ ⟨g, p.sigLen⟩)
    (d2 : Region.Disjoint ⟨k, kLS p pr⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨m, 64⟩ ⟨g, p.sigLen⟩) (d4 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d5 : Region.Disjoint ⟨r, 32⟩ ⟨g, p.sigLen⟩) (d6 : Region.Disjoint ⟨r, 32⟩ ⟨c, scratchWords p * 8⟩)
    (d7 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, kLS p pr⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨r, 32⟩) (b4 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩)
    (b5 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + kLS p pr ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : r.toNat + 32 ≤ 2 ^ 64)
    (f4 : g.toNat + p.sigLen ≤ 2 ^ 64) (f5 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64)
    (hx : pr = true → PreparedSecretKey p x.mem k) :
    (signK p pr PPC64LE.abi stk).pre x := by
  cases pr
  · simp only [signK, kLS, Bool.false_eq_true, ↓reduceIte] at *
    sig_pre [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [g3, g4, g5, g6, g7]
    and_intros
    -- Only the reserved stack depends on `stk`: split on it in those goals alone.
    all_goals first
      | with_reducible assumption
      | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil] <;> and_intros <;> first
          | with_reducible assumption | omega | skip)
      | omega
      | skip
    all_goals assumption
  · have hx' := hx rfl
    simp only [signK, kLS, ↓reduceIte] at *
    sig_pre [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [g3, g4, g5, g6, g7]
    and_intros
    all_goals first
      | with_reducible assumption
      | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil] <;> and_intros <;> first
          | with_reducible assumption | omega | skip)
      | omega
      | skip
    all_goals assumption

theorem sign_post {pr : Bool} (hp : (signK p pr PPC64LE.abi stk).post x y) :
    Outcome (fun b => signMu p b (bytesAt x.mem (x.gpr .r3) p.skLen) (bytesAt x.mem (x.gpr .r4) 64)
      (bytesAt x.mem (x.gpr .r5) 32)) ((y.gpr .r3).setWidth 32) (bytesAt y.mem (x.gpr .r6) p.sigLen) := by
  cases pr
  · simp only [signK, Bool.false_eq_true, ↓reduceIte] at hp
    sig_post [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs] at hp
    exact hp
  · simp only [signK, ↓reduceIte] at hp
    sig_post [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs] at hp
    exact hp

theorem sign_pub {pr : Bool} (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7)
    (hl : signLeak p (bytesAt x.mem (x.gpr .r3) p.skLen) (bytesAt x.mem (x.gpr .r4) 64)
        (bytesAt x.mem (x.gpr .r5) 32) =
      signLeak p (bytesAt y.mem (y.gpr .r3) p.skLen) (bytesAt y.mem (y.gpr .r4) 64)
        (bytesAt y.mem (y.gpr .r5) 32)) :
    (signK p pr PPC64LE.abi stk).pub x y := by
  cases pr
  · simp only [signK, Bool.false_eq_true, ↓reduceIte]
    sig_pub [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs]
    exact ⟨hsp, hl, h3, h4, h5, h6, h7⟩
  · simp only [signK, ↓reduceIte]
    sig_pub [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs]
    exact ⟨hsp, hl, h3, h4, h5, h6, h7⟩

theorem verify_pre {pr : Bool} {k m g c : Addr} (g3 : x.gpr .r3 = k) (g4 : x.gpr .r4 = m) (g5 : x.gpr .r5 = g)
    (g6 : x.gpr .r6 = c)
    (hrd : x.rd = [⟨k, kLV p pr⟩, ⟨m, 64⟩, ⟨g, p.sigLen⟩]) (hwr : x.wr = [⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat)
    (d1 : Region.Disjoint ⟨k, kLV p pr⟩ ⟨c, scratchWords p * 8⟩)
    (d2 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, kLV p pr⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩) (b4 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + kLV p pr ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : g.toNat + p.sigLen ≤ 2 ^ 64)
    (f4 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) (hx : pr = true → PreparedPublicKey p x.mem k) :
    (verifyK p pr PPC64LE.abi stk).pre x := by
  cases pr
  · simp only [verifyK, kLV, Bool.false_eq_true, ↓reduceIte] at *
    sig_pre [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [g3, g4, g5, g6]
    and_intros
    all_goals first
      | with_reducible assumption
      | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil] <;> and_intros <;> first
          | with_reducible assumption | omega | skip)
      | omega
      | skip
    all_goals assumption
  · have hx' := hx rfl
    simp only [verifyK, kLV, ↓reduceIte] at *
    sig_pre [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [g3, g4, g5, g6]
    and_intros
    all_goals first
      | with_reducible assumption
      | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil] <;> and_intros <;> first
          | with_reducible assumption | omega | skip)
      | omega
      | skip
    all_goals assumption

theorem verify_post {pr : Bool} (hp : (verifyK p pr PPC64LE.abi stk).post x y) :
    let v := fun b => verifyMu p b (bytesAt x.mem (x.gpr .r3) p.pkLen) (bytesAt x.mem (x.gpr .r4) 64)
      (bytesAt x.mem (x.gpr .r5) p.sigLen)
    ((y.gpr .r3).setWidth 32 = 1 ∧ ∃ b, v b = some true) ∨
      ((y.gpr .r3).setWidth 32 = 0 ∧ v minBounds ≠ some true) := by
  cases pr
  · simp only [verifyK, Bool.false_eq_true, ↓reduceIte] at hp
    sig_post [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs] at hp
    exact hp
  · simp only [verifyK, ↓reduceIte] at hp
    sig_post [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs] at hp
    exact hp

theorem verify_pub {pr : Bool} (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6)
    (hl : bytesAt x.mem (x.gpr .r3) p.pkLen ++ bytesAt x.mem (x.gpr .r4) 64 ++ bytesAt x.mem (x.gpr .r5) p.sigLen =
      bytesAt y.mem (y.gpr .r3) p.pkLen ++ bytesAt y.mem (y.gpr .r4) 64 ++ bytesAt y.mem (y.gpr .r5) p.sigLen) :
    (verifyK p pr PPC64LE.abi stk).pub x y := by
  cases pr
  · simp only [verifyK, Bool.false_eq_true, ↓reduceIte]
    sig_pub [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs]
    exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5, h6⟩
  · simp only [verifyK, ↓reduceIte]
    sig_pub [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs]
    exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5, h6⟩

end

end VG.Proof.MlDsa.PPC64LE.Message

end

end


/-!
# ML-DSA on PPC64LE, `sign_message`: correctness

From a state satisfying `MSPre`, `signMessage n f p` returns 2 if the
context string is longer than 255 bytes; otherwise it saves our caller's
registers in the 1 KiB at `E` (`MS1`), computes `μ` of the formatted message
into `840(E)` (`MS2`), and calls the signing function on `μ` `f`, which gives
the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_wp`). Between the steps, `Inv` records the arguments in
`r22`–`r30` and the saved registers, and that only `scratch`, `sig` and the
stack below the stack pointer change.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Message
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Impl.Ed25519.PPC64LE.Whole (saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea restore_ok restoreList)
open VG.Impl.Sha3.PPC64LE.Pieces (Piece Len hash)
open VG.Proof.Sha3.PPC64LE.Pieces (Kept PieceOk KEnv kW hash_ok)
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proofs need of the parameter set. -/
structure MFacts (p : Params) : Prop where
  e : oE p + 1024 < 2 ^ 31
  sk : 128 ≤ p.skLen
  pk : p.pkLen < 2 ^ 15
  skl : p.skLen < 2 ^ 15
  sgl : p.sigLen < 2 ^ 15
  psk : preparedSecretKeyBytes p < 2 ^ 15
  ppk : preparedPublicKeyBytes p < 2 ^ 15

theorem mfacts {p : Params} (h : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : MFacts p := by
  rcases h with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem MFacts.kls {p : Params} (hF : MFacts p) (pr : Bool) : 128 ≤ kLS p pr ∧ kLS p pr < 2 ^ 15 := by
  have := hF.sk; have := hF.skl; have := hF.psk
  cases pr <;> simp only [kLS, Bool.false_eq_true, ↓reduceIte] <;> simp only [preparedSecretKeyBytes] at * <;> omega_arith

theorem MFacts.klv {p : Params} (hF : MFacts p) (pr : Bool) : p.pkLen ≤ kLV p pr ∧ kLV p pr < 2 ^ 15 := by
  have := hF.pk; have := hF.ppk
  cases pr <;> simp only [kLV, Bool.false_eq_true, ↓reduceIte] <;> simp only [preparedPublicKeyBytes] at * <;> omega_arith

/-- A prepared private key, kept by a change of memory apart from it. -/
theorem preparedSecretKey_frame {p : Params} {m m' : Mem} {key : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨key, preparedSecretKeyBytes p⟩ : Region).Disjoint r)
    (hfit : key.toNat + preparedSecretKeyBytes p ≤ 2 ^ 64) (h : PreparedSecretKey p m key) :
    PreparedSecretKey p m' key := fun i hi => by
  obtain hb : p.skLen + 4 * n * i + 1024 ≤ preparedSecretKeyBytes p := by
    show p.skLen + 4 * 256 * i + 1024 ≤ p.skLen + 4 * 256 * (p.ℓ + 2 * p.k); omega_using [hi]
  obtain hk : bytesAt m' key p.skLen = bytesAt m key p.skLen := by
    obtain hs : Region.Sub ⟨key, p.skLen⟩ ⟨key, preparedSecretKeyBytes p⟩ := by
      have := Offset.sub_base key (d := 0) (n := p.skLen) (k := preparedSecretKeyBytes p) (by omega_using [hb])
      rwa [BitVec.add_zero] at this
    exact Proof.MlKem.bytesAt_frame hf (fun r hr => (hd r hr).sub_left hs) (by omega_using [hfit, hb])
  rw [hk]
  obtain hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (key + BitVec.ofNat 64 (p.skLen + 4 * n * i)))
      ⟨key, preparedSecretKeyBytes p⟩ := Offset.sub_base _ hb
  exact Proof.MlDsa.polyStored_iff.mpr (Proof.MlDsa.Verify.polyIs_frame hf (fun r hr => (hd r hr).sub_left hsub)
    (Proof.MlDsa.polyStored_iff.mp (h i hi)))

/-- A prepared public key, kept by a change of memory apart from it. -/
theorem preparedPublicKey_frame {p : Params} {m m' : Mem} {key : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨key, preparedPublicKeyBytes p⟩ : Region).Disjoint r)
    (hfit : key.toNat + preparedPublicKeyBytes p ≤ 2 ^ 64) (h : PreparedPublicKey p m key) :
    PreparedPublicKey p m' key := fun i hi => by
  obtain hb : p.pkLen + 4 * n * i + 1024 ≤ preparedPublicKeyBytes p := by
    show p.pkLen + 4 * 256 * i + 1024 ≤ p.pkLen + 4 * 256 * (p.k); omega_using [hi]
  obtain hk : bytesAt m' key p.pkLen = bytesAt m key p.pkLen := by
    obtain hs : Region.Sub ⟨key, p.pkLen⟩ ⟨key, preparedPublicKeyBytes p⟩ := by
      have := Offset.sub_base key (d := 0) (n := p.pkLen) (k := preparedPublicKeyBytes p) (by omega_using [hb])
      rwa [BitVec.add_zero] at this
    exact Proof.MlKem.bytesAt_frame hf (fun r hr => (hd r hr).sub_left hs) (by omega_using [hfit, hb])
  rw [hk]
  obtain hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (key + BitVec.ofNat 64 (p.pkLen + 4 * n * i)))
      ⟨key, preparedPublicKeyBytes p⟩ := Offset.sub_base _ hb
  exact Proof.MlDsa.polyStored_iff.mpr (Proof.MlDsa.Verify.polyIs_frame hf (fun r hr => (hd r hr).sub_left hsub)
    (Proof.MlDsa.polyStored_iff.mp (h i hi)))

theorem msw (p : Params) : messageScratchWords p * 8 = oE p + 1024 := by
  simp only [messageScratchWords, oE]; omega_arith

theorem e_len (p : Params) {d n : Nat} (h : d + n ≤ 1024) : oE p + d + n ≤ messageScratchWords p * 8 := by
  rw [msw]; omega_arith

/-- A region of the 1 KiB does not wrap around. -/
theorem e_fit {p : Params} {x : Addr} (hx : x.toNat + messageScratchWords p * 8 ≤ 2 ^ 64) {d n : Nat}
    (hn : 0 < n) (h : d + n ≤ 1024) : (x + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  have := e_len p h
  rw [Proof.MlDsa.Message.add_add, Proof.MlDsa.Message.toNat_add_ofNat (by omega_arith)]; omega_arith

/-! ## The 1 KiB -/

/-- `E`, from `scratch` in `r` of the entry state. -/
abbrev eAt (p : Params) (x : Addr) : Addr := x + BitVec.ofNat 64 (oE p)

theorem e_add (p : Params) (x : Addr) (d : Nat) :
    eAt p x + BitVec.ofNat 64 d = x + BitVec.ofNat 64 (oE p + d) :=
  Proof.MlDsa.Message.add_add _ _ _

section
variable {p : Params} {x : Addr}

/-- A region in the 1 KiB lies in `scratch`. -/
theorem e_sub {d n : Nat} (h : d + n ≤ 1024) :
    Region.Sub ⟨eAt p x + BitVec.ofNat 64 d, n⟩ ⟨x, messageScratchWords p * 8⟩ := by
  rw [e_add]; exact Offset.sub_base _ (by rw [msw]; omega_arith)

theorem e_sub0 {n : Nat} (h : n ≤ 1024) : Region.Sub ⟨eAt p x, n⟩ ⟨x, messageScratchWords p * 8⟩ := by
  have := e_sub (p := p) (x := x) (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at this

/-- The working space of the function on `μ` lies in `scratch`. -/
theorem w_sub : Region.Sub ⟨x, scratchWords p * 8⟩ ⟨x, messageScratchWords p * 8⟩ :=
  Region.sub_prefix (by simp only [messageScratchWords]; omega_arith)

/-- A region in the 1 KiB lies apart from the working space of the function on `μ`. -/
theorem e_w {d n : Nat} (hp : MFacts p) (h : d + n ≤ 1024) :
    Region.Disjoint ⟨x, scratchWords p * 8⟩ ⟨eAt p x + BitVec.ofNat 64 d, n⟩ := by
  have := hp.e
  rw [e_add]; exact Offset.base_disjoint _ (by simp only [oE]; omega_arith) (by omega_arith)

/-- Two regions of the 1 KiB. -/
theorem e_e {d n d' n' : Nat} (h : d + n ≤ d' ∨ d' + n' ≤ d) (h₁ : d + n ≤ 1024) (h₂ : d' + n' ≤ 1024) :
    Region.Disjoint ⟨eAt p x + BitVec.ofNat 64 d, n⟩ ⟨eAt p x + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint _ h (by omega_arith) (by omega_arith)

theorem e_e0 {n d' n' : Nat} (h : n ≤ d') (h₂ : d' + n' ≤ 1024) :
    Region.Disjoint ⟨eAt p x, n⟩ ⟨eAt p x + BitVec.ofNat 64 d', n'⟩ :=
  Offset.disjoint_base _ h (by omega_arith) |>.symm

end

/-! ## The invariant -/

/-- What the registers hold: the arguments, and `E`. -/
def signV (p : Params) (s : State) : Reg → BitVec 64
  | .r22 => s.gpr .r3 | .r23 => s.gpr .r4 | .r24 => s.gpr .r5 | .r25 => s.gpr .r6 | .r26 => s.gpr .r7
  | .r27 => s.gpr .r8 | .r28 => s.gpr .r9 | .r29 => s.gpr .r10 | .r30 => eAt p (s.gpr .r10) | _ => 0

/-- What the body may write. -/
abbrev sW (p : Params) (STK : Nat) (s : State) : List Region := [scrR p s, sigR p s, below s.sp STK]

abbrev SInv (p : Params) (STK : Nat) (s : State) : State → Prop :=
  Inv s (eAt p (s.gpr .r10)) oSV signRegs (signV p s) (sW p STK s)

theorem signRegs_pres : ∀ r ∈ signRegs, r ∈ preserved := by decide

section
variable {p : Params} {pr : Bool} {STK : Nat} {s : State} (hF : MFacts p) (hp : MSPre p pr STK s) (h48 : 48 ≤ STK)

theorem s_e {t : State} (h : SInv p STK s t) : t.gpr .r30 = eAt p (s.gpr .r10) := h.regs _ (by decide)

/-- The slots, in `scratch` and apart from what the body writes there. -/
theorem slot_sub : Region.Sub (slotArea (eAt p (s.gpr .r10)) oSV signRegs) (scrR p s) := e_sub (by decide)

theorem slot_e {d n : Nat} (h : d + n ≤ oSV ∨ oSV + 80 ≤ d) (h₁ : d + n ≤ 1024) :
    (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 d, n⟩ :=
  e_e (h.symm.imp id id) (by decide) h₁

include hF in
theorem slot_w : (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint ⟨s.gpr .r10, scratchWords p * 8⟩ :=
  (e_w hF (by decide)).symm

include hp in
theorem slot_g : (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint (sigR p s) :=
  hp.gc.symm.sub_left slot_sub

include hp h48 in
theorem below48 : Region.Sub (below s.sp 48) (below s.sp STK) := below_sub h48 (by have := hp.stk; omega_arith)

include hp h48 in
theorem slot_b : (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint (below s.sp 48) :=
  (hp.bx.symm.sub_left slot_sub).sub_right (below48 hp h48)

include hF hp in
theorem e_in {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    InRegions t.wr (eAt p (s.gpr .r10) + BitVec.ofNat 64 d) n := by
  rw [hw, hp.wr, e_add]
  exact in_base (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [msw]; omega_arith)
    (by have := hF.e; omega_arith)

include hp in
/-- A region of the 1 KiB, writable. -/
theorem e_cov {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    PPC64LE.Covers [⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 d, n⟩] t.wr := by
  rw [hw, hp.wr]
  refine Covers.of_sub fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ⟨scrR p s, List.mem_cons_of_mem _ List.mem_cons_self, oE p + d, e_add _ _ _, by
    simp only [msw]; omega_arith⟩

include hp in
theorem e_cov0 {t : State} (hw : t.wr = s.wr) {n : Nat} (h : n ≤ 1024) :
    PPC64LE.Covers [⟨eAt p (s.gpr .r10), n⟩] t.wr := by
  have := e_cov hp hw (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at this

theorem slot_e0 {n : Nat} (h : n ≤ oSV) :
    (slotArea (eAt p (s.gpr .r10)) oSV signRegs).Disjoint ⟨eAt p (s.gpr .r10), n⟩ :=
  (e_e0 h (by decide)).symm

/-- The inputs, while the body runs: none of them is in `sW`. -/
theorem s_keep {t : State} (h : SInv p STK s t) {R : Region} (hn : R.len < 2 ^ 64)
    (hg : R.Disjoint (sigR p s)) (hc : R.Disjoint (scrR p s)) (hb : (below s.sp STK).Disjoint R) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine Proof.Sha3.PPC64LE.Pieces.bytes_keep h.frame hn fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hc
  · exact hg
  · exact hb.symm

end

/-! ## The setup -/

/-- After the setup: the invariant, and `0 ‖ ctx_len` at `oHdr(E)`. -/
structure MS1 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : SInv p STK s t
  hdr : bytesAt t.mem (eAt p (s.gpr .r10) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .r7).toNat]

/-- `E` into `r12`, from `scratch` in `sr`. -/
theorem base_ok (p : Params) (hF : MFacts p) {sr : Reg} (hsr : sr ≠ .r12) (u : State) :
    WP isa (.block (base sr p)) u fun u' => Upd u u' .r12 (eAt p (u.gpr sr)) ∧ u'.lr = u.lr := by
  unfold base
  refine WP.block_append_iff.mpr (WP.mono (KeyGen.loadImm_ok .r12 (by have := hF.e; omega_arith) u) fun u₁ e₁ => ?_)
  subst e₁
  refine WP.cons exec_add (WP.block_nil ⟨⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ hsr, RegUpd.gpr_write_self]
  · rw [RegUpd.gpr_write_of_ne _ _ hr, RegUpd.gpr_write_of_ne _ _ hr]

theorem signSetup_ok {p : Params} {pr : Bool} {STK : Nat} {s u : State} (hF : MFacts p) (hp : MSPre p pr STK s)
    (hu : ∀ r, r ≠ .r11 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsp : u.sp = s.sp)
    (hlr : u.lr = s.lr) (hm : u.mem = s.mem) :
    WP isa (.block (enter .r10 p signRegs signMs)) u (MS1 p STK s) := by
  unfold enter
  refine WP.block_append_iff.mpr (WP.mono (base_ok p hF (by decide) u) fun u₁ ⟨h₁, l₁⟩ => ?_)
  obtain g10 : u.gpr .r10 = s.gpr .r10 := hu _ (by decide)
  rw [g10] at h₁
  obtain hw₁ : u₁.wr = s.wr := h₁.wr.trans hwr
  refine setup_ok (v := signV p s) (W := sW p STK s) (by decide) (by decide) (by decide)
    (fun q hq => by rw [h₁.gpr]; exact e_in hF hp hw₁ (by revert q; decide))
    ⟨scrR p s, by simp, by rw [h₁.gpr]; exact slot_sub⟩ rfl (by decide) (by decide) (fun q hq => by
      simp only [signMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 8 exact ((h₁.other _ (by decide)).trans (hu _ (by decide))).symm
      exact h₁.gpr.symm)
    fun t₁ i₁ => ?_
  rw [h₁.gpr] at i₁
  obtain i₁ : SInv p STK s t₁ := inv_rebase i₁ signRegs_pres (h₁.rd.trans hrd) hw₁ (h₁.sp.trans hsp) (l₁.trans hlr)
    (fun r hr => (h₁.other r fun e => by revert hr; rw [e]; decide).trans (hu r fun e => by revert hr; rw [e]; decide))
    (h₁.mem.trans hm)
  obtain g30 : t₁.gpr .r30 = eAt p (s.gpr .r10) := i₁.regs _ (by decide)
  obtain g26 : t₁.gpr .r26 = s.gpr .r7 := i₁.regs _ (by decide)
  refine hdr_ok (o := oHdr) (by decide) (by decide) (by decide) (by rw [g30]; exact e_in hF hp i₁.wr (by decide))
    (by rw [g30]; exact e_in hF hp i₁.wr (by decide)) fun t ht hrd' hwr' hsp' hg => WP.block_nil ⟨?_, ?_⟩
  · refine i₁.step signRegs_pres hrd' hwr' hsp' (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr, g30]; exact ⟨scrR p s, by simp, e_sub (by decide)⟩
    · rw [List.mem_singleton.mp hr, g30]; exact slot_e (.inr (by decide)) (by decide)
  · rw [ht, g30, g26, show s.gpr .r7 = BitVec.ofNat 64 (s.gpr .r7).toNat by simp, hdrMem_bytes]
    simp

/-! ## `μ` -/

section
variable (p : Params) (s : State)

/-- The inputs. -/
abbrev skB : List Byte := bytesAt s.mem (s.gpr .r3) p.skLen
abbrev msgB : List Byte := bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat
abbrev ctxB : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev rndB : List Byte := bytesAt s.mem (s.gpr .r8) 32

/-- The formatted message. -/
abbrev fmtB : List Byte := [0, BitVec.ofNat 8 (s.gpr .r7).toNat] ++ ctxB s ++ msgB s

end

/-- After `μ`: the invariant, and `μ` at `oMU(E)`. -/
structure MS2 (p : Params) (STK : Nat) (s t : State) : Prop where
  inv : SInv p STK s t
  mu : bytesAt t.mem (eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU) 64 = messageRep (skTr (skB p s)) (fmtB s)

/-- Where the hash of `μ` may run, from the invariant. -/
theorem signHash_env {p : Params} {pr : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p pr STK s) (h48 : 48 ≤ STK)
    (hi : SInv p STK s t) : KEnv 840 (eAt p (s.gpr .r10)) t ∧
      ∀ q ∈ (⟨.r22, 64, .imm 64⟩ : Piece) :: fmtPieces, PieceOk 840 (eAt p (s.gpr .r10)) t q := by
  obtain g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  obtain g23 : t.gpr .r23 = s.gpr .r4 := hi.regs _ (by decide)
  obtain g24 : t.gpr .r24 = s.gpr .r5 := hi.regs _ (by decide)
  obtain g25 : t.gpr .r25 = s.gpr .r6 := hi.regs _ (by decide)
  obtain g26 : t.gpr .r26 = s.gpr .r7 := hi.regs _ (by decide)
  obtain g30 := s_e hi
  obtain hsk := (hF.kls pr).1
  have hsk' := hF.sk
  obtain b48 := below48 hp h48
  have hsp : t.sp = s.sp := hi.sp
  obtain trS : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩ (skR p pr s) := Offset.sub_base _ (by omega_arith)
  obtain eS := e_sub0 (p := p) (x := s.gpr .r10) (n := 840) (by decide)
  obtain cr : ∀ R ∈ [skR p pr s, msgR s, ctxR s, rndR s], PPC64LE.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hR, hc⟩
  obtain ke : KEnv 840 (eAt p (s.gpr .r10)) t :=
    ⟨by decide, e_cov0 hp hi.wr (by decide), by rw [hsp]; have := hp.stk; omega_arith,
      by rw [hsp]; exact (hp.bx.sub_left b48).sub_right eS⟩
  obtain hin : ∀ q ∈ (⟨.r22, 64, .imm 64⟩ : Piece) :: fmtPieces, PieceOk 840 (eAt p (s.gpr .r10)) t q := by
    intro q hq
    simp only [fmtPieces, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact pieceOk_of (R := ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩)
        (by simp only [Piece.R, Piece.addr, Len.val, g22]) (by decide) (by decide) (show 64 < 2 ^ 15 by decide)
        (cov_rd (cov_in (k := kLS p pr) (by rw [hi.rd, hp.rd]; simp) (by omega_arith)))
        ((hp.kc.sub_left trS).sub_right eS) (by rw [hsp]; exact (hp.bk.sub_left b48).sub_right trS)
    · exact pieceOk_of (R := ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oHdr, 2⟩)
        (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 2 < 2 ^ 15 by decide)
        (Proof.Sha3.PPC64LE.Pieces.cov_right (e_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
        (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
    · exact pieceOk_of (R := ctxR s) (by simp only [Piece.R, Piece.addr, Len.val, g25, g26, BitVec.add_zero])
        (by decide) (by decide) (show Reg.r26 ∈ preserved by decide) (cr _ (by simp))
        (hp.cc.sub_right eS) (by rw [hsp]; exact hp.bc.sub_left b48)
    · exact pieceOk_of (R := msgR s) (by simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero])
        (by decide) (by decide) (show Reg.r24 ∈ preserved by decide) (cr _ (by simp))
        (hp.mc.sub_right eS) (by rw [hsp]; exact hp.bm.sub_left b48)
  exact ⟨ke, hin⟩

theorem signHash_ok {p : Params} {pr : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p pr STK s) (h48 : 48 ≤ STK)
    (h : MS1 p STK s t) : WP isa (muHash ⟨.r22, 64, .imm 64⟩) t (MS2 p STK s) := by
  have hi := h.inv
  obtain ⟨ke, hin⟩ := signHash_env hF hp h48 hi
  obtain g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  obtain g23 : t.gpr .r23 = s.gpr .r4 := hi.regs _ (by decide)
  obtain g24 : t.gpr .r24 = s.gpr .r5 := hi.regs _ (by decide)
  obtain g25 : t.gpr .r25 = s.gpr .r6 := hi.regs _ (by decide)
  obtain g26 : t.gpr .r26 = s.gpr .r7 := hi.regs _ (by decide)
  obtain g30 := s_e hi
  obtain hsk := (hF.kls pr).1
  have hsk' := hF.sk
  obtain b48 := below48 hp h48
  have hsp : t.sp = s.sp := hi.sp
  obtain trS : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩ (skR p pr s) := Offset.sub_base _ (by omega_arith)
  obtain eS := e_sub0 (p := p) (x := s.gpr .r10) (n := 840) (by decide)
  unfold muHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU) (by decide) (by decide) (by decide) (by decide) g30
    (by rw [g30]) ke (by simp) hin (e_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_⟩
  · refine inv_kept hi signRegs_pres k' (fun r hr => ?_) fun r hr => ?_
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR p s, by simp, e_sub (by decide)⟩
      · exact ⟨scrR p s, by simp, eS⟩
      · exact ⟨below s.sp STK, by simp, by rw [hsp]; exact b48⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_e (.inl (by decide)) (by decide)
      · exact slot_e0 (by decide)
      · rw [hsp]; exact slot_b hp h48
  · rw [d']
    obtain kt : bytesAt t.mem (s.gpr .r3 + BitVec.ofNat 64 64) 64 = skTr (skB p s) := by
      rw [s_keep hi (R := ⟨s.gpr .r3 + BitVec.ofNat 64 64, 64⟩) (show (64 : Nat) < 2 ^ 64 by decide) (hp.kg.sub_left trS)
        (hp.kc.sub_left trS) ((hp.bk.symm.sub_left trS).symm), skTr, Proof.MlKem.bytesAt_slice _ _ (by omega_arith)]
    obtain kc : bytesAt t.mem (s.gpr .r6) (s.gpr .r7).toNat = ctxB s :=
      s_keep hi (R := ctxR s) (BitVec.isLt _) hp.cg hp.cc hp.bc
    obtain km : bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat = msgB s :=
      s_keep hi (R := msgR s) (BitVec.isLt _) hp.mg hp.mc hp.bm
    have hh := h.hdr
    simp only [fmtPieces, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Piece.bytes, Piece.addr, Len.val, g22, g23, g24, g25, g26, g30, BitVec.add_zero]
    rw [kt, hh, kc, km]
    simp only [messageRep, H, List.append_assoc]

/-! ## The call of the signing function on `μ` -/

theorem ce_gpr (u : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (u.callEntry.withRegions rd wr).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The arguments of the call. -/
abbrev signArgs : List Instr := [mov .r3 .r22, .addi .r4 .r30 oMU, mov .r5 .r27, mov .r6 .r28, mov .r7 .r29]

/-- After the arguments of the call: `μ`, and the arguments in `r3`–`r7`. -/
structure SA (p : Params) (STK : Nat) (s u : State) : Prop where
  ms : MS2 p STK s u
  r3 : u.gpr .r3 = s.gpr .r3
  r4 : u.gpr .r4 = eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU
  r5 : u.gpr .r5 = s.gpr .r8
  r6 : u.gpr .r6 = s.gpr .r9
  r7 : u.gpr .r7 = s.gpr .r10

theorem signArgs_ok {p : Params} {STK : Nat} {s t : State} (h : MS2 p STK s t) :
    WP isa (.block signArgs) t (SA p STK s) := by
  have hi := h.inv
  obtain g22 : t.gpr .r22 = s.gpr .r3 := hi.regs _ (by decide)
  obtain g27 : t.gpr .r27 = s.gpr .r8 := hi.regs _ (by decide)
  obtain g28 : t.gpr .r28 = s.gpr .r9 := hi.regs _ (by decide)
  obtain g29 : t.gpr .r29 = s.gpr .r10 := hi.regs _ (by decide)
  obtain g30 := s_e hi
  unfold signArgs mov
  refine Ed25519.PPC64LE.Whole.args5_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun u hu a3 a4 a5 a6 a7 =>
    ⟨⟨hi.step signRegs_pres hu.rd hu.wr hu.sp hu.pres (by rw [hu.mem]; exact Frame.refl _ _)
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), by rw [hu.mem]; exact h.mu⟩,
      ?_, ?_, ?_, ?_, ?_⟩
  · rw [a3, g22, BitVec.add_zero]
  · rw [a4, g30]
  · rw [a5, g27, BitVec.add_zero]
  · rw [a6, g28, BitVec.add_zero]
  · rw [a7, g29, BitVec.add_zero]

/-- What the signing function on `μ` reads and writes. -/
abbrev sRd (p : Params) (pr : Bool) (s : State) : List Region :=
  [skR p pr s, ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU, 64⟩, rndR s]
abbrev sWr (p : Params) (s : State) : List Region := [sigR p s, ⟨s.gpr .r10, scratchWords p * 8⟩]

/-- The call's precondition, and its regions. -/
theorem signCall_pre {p : Params} {pr : Bool} {STK stk : Nat} {s u : State} (hF : MFacts p) (hp : MSPre p pr STK s)
    (hstk : stk ≤ STK) (h : SA p STK s u) :
    (signK p pr PPC64LE.abi stk).pre (u.callEntry.withRegions (sRd p pr s) (sWr p s)) ∧
      PPC64LE.Covers (sRd p pr s ++ sWr p s) (u.rd ++ u.wr) ∧ PPC64LE.Covers (sWr p s) u.wr := by
  have iu := h.ms.inv
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  have hE := hF.e
  have fx := hp.fx
  rw [msw] at fx
  have usp : u.sp = s.sp := iu.sp
  have urd : u.rd = s.rd := iu.rd
  have uwr : u.wr = s.wr := iu.wr
  obtain bs : Region.Sub (below s.sp stk) (below s.sp STK) := below_sub (by omega_arith) (by omega_arith)
  obtain muS : Region.Sub ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU, 64⟩ (scrR p s) := e_sub (by decide)
  obtain muW : Region.Disjoint ⟨s.gpr .r10, scratchWords p * 8⟩ ⟨eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU, 64⟩ :=
    e_w hF (by decide)
  obtain muF : (eAt p (s.gpr .r10) + BitVec.ofNat 64 oMU).toNat + 64 ≤ 2 ^ 64 := e_fit hp.fx (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · refine sign_pre ((ce_gpr _ _ _ (by decide)).trans h.r3) ((ce_gpr _ _ _ (by decide)).trans h.r4)
      ((ce_gpr _ _ _ (by decide)).trans h.r5) ((ce_gpr _ _ _ (by decide)).trans h.r6)
      ((ce_gpr _ _ _ (by decide)).trans h.r7) rfl rfl (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; omega_arith)
      hp.kg (hp.kc.sub_right w_sub) (hp.gc.symm.sub_left muS) muW.symm hp.rg (hp.rc.sub_right w_sub)
      (hp.gc.sub_right w_sub) ?_ ?_ ?_ ?_ ?_ hp.fk muF hp.fr hp.fg (by have : scratchWords p * 8 ≤ oE p := (by simp only [oE]; omega_arith); omega_arith)
      (fun hpr => by
        subst hpr
        simp only [State.withRegions_mem, State.callEntry_mem]
        exact preparedSecretKey_frame iu.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          exacts [hp.kc, hp.kg, hp.bk.symm]) hp.fk (hp.x rfl))
    all_goals simp only [State.withRegions_sp, State.callEntry_sp, usp]
    · exact hp.bk.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right muS
    · exact hp.br.sub_left bs
    · exact hp.bg.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right w_sub
  · rw [urd, uwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨skR p pr s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, oE p + oMU, e_add _ _ _, e_len p (d := oMU) (n := 64) (by decide)⟩
    · exact ⟨rndR s, by simp, 0, by simp, by simp⟩
    · exact ⟨sigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, 0, by simp, by simp only [messageScratchWords]; omega_arith⟩
  · rw [uwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR p s, by simp, 0, by simp, by simp only [messageScratchWords]; omega_arith⟩

theorem signCall_ok {p : Params} {pr : Bool} {STK S : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p pr STK s)
    {f : Prog isa} (hf : Callee f (fun stk => signK p pr PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String}
    (h : MS2 p STK s t) :
    WP isa (.seq (.block signArgs) (.call n f)) t fun t' => SInv p STK s t' ∧
      Outcome (fun b => signMu p b (skB p s) (messageRep (skTr (skB p s)) (fmtB s)) (rndB s))
        ((t'.gpr .r3).setWidth 32) (bytesAt t'.mem (s.gpr .r9) p.sigLen) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  refine WP.seq (WP.mono (signArgs_ok h) fun u hu => ?_)
  have iu := hu.ms.inv
  have usp : u.sp = s.sp := iu.sp
  obtain ⟨hpre, hc, hw⟩ := signCall_pre hF hp (Nat.le_trans hstk hS) hu
  obtain hd : sdepth f < 2 ^ 64 := by have := hf.stack; omega_arith
  refine WP.callAny hver.1 hpre hc hw (fun s' rd' wr' sp' fr' cs' post' => ?_) hd
  refine ⟨iu.step signRegs_pres rd' wr' sp' cs' fr' (fun r hr => ?_) fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sigR p s, by simp, fun _ h => h⟩
    · exact ⟨scrR p s, by simp, w_sub⟩
    · exact ⟨below s.sp STK, by simp, by rw [usp]; exact below_sub (by have := hf.stack; omega_arith) (by omega_arith)⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_g hp
    · exact slot_w hF
    · rw [usp]
      exact (hp.bx.symm.sub_left slot_sub).sub_right (below_sub (by have := hf.stack; omega_arith) (by omega_arith))
  · have q := sign_post post'
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
      hu.r3, hu.r4, hu.r5, hu.r6] at q
    rw [s_keep iu (R := ⟨s.gpr .r3, p.skLen⟩) (by have := hF.skl; show p.skLen < 2 ^ 64; omega_arith)
      (hp.kg.sub_left hp.subK) (hp.kc.sub_left hp.subK) (hp.bk.sub_right hp.subK), hu.ms.mu,
      s_keep iu (R := rndR s) (show (32 : Nat) < 2 ^ 64 by decide) hp.rg hp.rc hp.br] at q
    exact q

/-! ## `sign_message` -/

/-- The result: 2 for a context string longer than 255 bytes, else the
signature of the formatted message. -/
theorem signMessage_wp {p : Params} {pr : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 48 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => signK p pr PPC64LE.abi stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hp : MSPre p pr STK s) :
    WP isa (signMessage n f p) s fun t => abiPreserved s t ∧ (msgSK p pr PPC64LE.abi STK).post s t := by
  unfold signMessage top
  refine WP.seq (WP.cons (exec_lsr_d (by decide)) (WP.block_nil ?_))
  obtain hu := Upd.write s .r11 (s.gpr .r7 >>> 8)
  refine wp_ite (decide ((s.gpr .r7).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _)) (fun hcl => ?_)
    fun hcl => ?_
  · have hcl' : (s.gpr .r7).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (signSetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (signHash_ok hF hp h48 h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (signCall_ok hF hp hf hS h₂) fun t₃ ⟨h₃, r₃⟩ => ?_)
    obtain hrl : ∀ q ∈ restoreList oSV signRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₃ (by decide) (s_e h₃) (by decide) (by decide) (by decide) (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega_arith)
        have := hF.e
        rw [h₃.rd, h₃.wr, hp.rd, hp.wr, e_add]
        exact ⟨scrR p s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₄ g₄ sp₄ lr₄ m₄ o₄ => ⟨⟨g₄, sp₄, lr₄⟩, ?_⟩
    · cases pr <;> simp only [msgSK, Bool.false_eq_true, ↓reduceIte]
      all_goals
        sig_post [signMessageContract, signMessageSig, preparedSignMessageContract, preparedSignMessageSig,
          PPC64LE.abi, PPC64LE.argRegs]
        rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'), o₄ .r3 (by decide)
          (by decide), m₄]
        simp only [signInternal, Proof.MlKem.bytesAt_length]
        exact r₃
  · have hcl' : ¬ (s.gpr .r7).toNat < 256 := of_decide_eq_false hcl
    refine WP.cons (exec_li (d := .r3) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Upd.write _ _ _).other _ (Proof.Sha3.PPC64LE.Pieces.pres_ne hr).2.1, hu.other _ (by revert hr; cases r <;> decide)]
    · cases pr <;> simp only [msgSK, Bool.false_eq_true, ↓reduceIte]
      all_goals
        sig_post [signMessageContract, signMessageSig, preparedSignMessageContract, preparedSignMessageSig,
          PPC64LE.abi, PPC64LE.argRegs]
        rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_arith)]
        rfl

end VG.Proof.MlDsa.PPC64LE.Message
