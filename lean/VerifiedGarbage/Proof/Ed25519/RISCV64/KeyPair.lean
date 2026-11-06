module

public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.RISCV64.KeyPair
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# Ed25519 key-pair derivation on RISCV64

`keyPair` calls the one-shot SHA-512 digest (`vg_sha512_digest`), which
writes the seed's digest to `expanded`, and then
`vg_ed25519_public_key_expanded`, which derives the public key from it. Its
proof uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`sp - 480` on entry): the frame is at `K s + 448` (the
return address, then `out`, `expanded` and `scratch`), and both calls enter
with `sp = K s + 448`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.KeyPair

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Impl.Ed25519.RISCV64.KeyPair

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (RISCV64.abi.withConsts combConsts) 480

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := s.sp - BitVec.ofNat 64 480

abbrev OUT (s : State) : Region := ⟨s.gpr .a0, 32⟩
abbrev EXP (s : State) : Region := ⟨s.gpr .a1, 64⟩
abbrev SEED (s : State) : Region := ⟨s.gpr .a2, 32⟩
abbrev SCR (s : State) : Region := ⟨s.gpr .a3, 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 480⟩
abbrev TB (s : State) : Region := ⟨s.syms combSym, 8 * combWords.length⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp : 480 ≤ s.sp.toNat
  rd : s.rd = [SEED s, TB s]
  wr : s.wr = [OUT s, EXP s, SCR s]
  held : ∀ i < combWords.length,
    s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0
  fit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64
  al : (s.syms combSym).toNat % 64 = 0
  tO : (TB s).Disjoint (OUT s)
  tE : (TB s).Disjoint (EXP s)
  tC : (TB s).Disjoint (SCR s)
  tK : (TB s).Disjoint (STK s)
  oe : (OUT s).Disjoint (EXP s)
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  es : (EXP s).Disjoint (SEED s)
  ec : (EXP s).Disjoint (SCR s)
  sc : (SEED s).Disjoint (SCR s)
  ko : (STK s).Disjoint (OUT s)
  ke : (STK s).Disjoint (EXP s)
  ks : (STK s).Disjoint (SEED s)
  kc : (STK s).Disjoint (SCR s)
  no : (s.gpr .a0).toNat + 32 ≤ 2 ^ 64
  ne : (s.gpr .a1).toNat + 64 ≤ 2 ^ 64
  ns : (s.gpr .a2).toNat + 32 ≤ 2 ^ 64
  nc : (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨hspal, hsp, hd, hheld, hfit, hdw, hdk, hal, ht, hw, oe, os, oc, es, ec, sc,
    ko, ke, ks, kc, no, ne, ns, nc⟩ := h
  refine ⟨hspal, hsp, ?_, hw, hheld, hfit, hal, hdw _ (by rw [hw]; simp), hdw _ (by rw [hw]; simp),
    hdw _ (by rw [hw]; simp), hdk, oe, os, oc, es, ec, sc, ko, ke, ks, kc, no, ne, ns, nc⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl

/-- The precondition, from its facts. -/
theorem spec_of {s : State} (h : Pre s) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  refine ⟨h.spal, h.sp, by rw [h.rd]; rfl, h.held, h.fit, fun r hr => ?_, h.tK, h.al, by rw [h.rd]; rfl, h.wr,
    h.oe, h.os, h.oc, h.es, h.ec, h.sc, h.ko, h.ke, h.ks, h.kc, h.no, h.ne, h.ns, h.nc⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.tO
  · exact h.tE
  · exact h.tC

/-! ## Addresses on the stack -/

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) :
    p + BitVec.ofNat 64 a - BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a - b) := by
  rw [Offset.sub_ofNat_eq (p + BitVec.ofNat 64 a) (show b ≤ a from h), BitVec.add_sub_cancel]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sp_eq (s : State) : s.sp = K s + BitVec.ofNat 64 480 := by
  simp only [K, BitVec.sub_add_cancel]

theorem sp32 (s : State) : s.sp - BitVec.ofNat 64 32 = K s + BitVec.ofNat 64 448 := by
  rw [sp_eq s]; exact off_sub _ (by decide)

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 480) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

theorem K_toNat {s : State} (h : Pre s) {d : Nat} (hd : d ≤ 480) :
    (K s + BitVec.ofNat 64 d).toNat = (K s).toNat + d := by
  have hk : (K s).toNat + 480 = s.sp.toNat := by
    have := h.sp
    simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have := s.sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 480) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 480) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 480) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 480) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 480) : Region.Disjoint (TB s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  h.tK.sub_right (stk_sub s hd)

end Pre

/-! ## Within the frame -/

/-- The frame. -/
abbrev AR (s : State) : Region := ⟨K s + BitVec.ofNat 64 448, 32⟩

/-- What holds within the frame, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = AR s :: s.wr
  sp : t.sp = K s + BitVec.ofNat 64 448
  cs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  ra : t.mem.readW (K s + BitVec.ofNat 64 448) 64 = s.gpr .ra
  fOut : t.mem.readW (K s + BitVec.ofNat 64 456) 64 = s.gpr .a0
  fExp : t.mem.readW (K s + BitVec.ofNat 64 464) 64 = s.gpr .a1
  fScr : t.mem.readW (K s + BitVec.ofNat 64 472) 64 = s.gpr .a3
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

/-- A write of a register the ABI does not preserve. -/
theorem Ctx.write {s t : State} (hc : Ctx s t) {r : Reg} (hr : r ∉ preserved) (x : BitVec 64) :
    Ctx s (t.write r x) :=
  ⟨hc.rd, hc.wr, hc.sp, fun q hq => by
      have hne : ¬q = r := fun e => hr (e ▸ hq)
      rw [RegUpd.gpr_write_of_ne (h := hne)]; exact hc.cs q hq,
    hc.ra, hc.fOut, hc.fExp, hc.fScr, hc.sym, hc.frame⟩

theorem exec_addSp0 (t : State) : exec (.addSp .t0 0) t = some (t.write .t0 (t.sp + BitVec.ofNat 64 0)) :=
  exec_addSp (by decide)

theorem Ctx.inAR {s t : State} (hc : Ctx s t) {d : Nat} (hd : d + 8 ≤ 32) :
    InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 d) 8 := by
  rw [hc.wr, hc.sp, add_add, add_add]
  exact ⟨AR s, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- The frame's doublewords are aligned. -/
theorem al8 {s : State} (h : Pre s) {x : Addr} (hx : x = K s + BitVec.ofNat 64 448) {d : Nat} (hd : d % 8 = 0)
    (hd' : d + 8 ≤ 32) : (x + BitVec.ofNat 64 0 + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [hx, add_add, add_add, K_toNat h (by omega)]
  have := h.spal
  have := h.sp
  simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  omega

theorem Ctx.sp16 {s t : State} (h : Pre s) (hc : Ctx s t) : t.sp.toNat % 16 = 0 := by
  rw [hc.sp, K_toNat h (by decide)]
  have := h.spal
  have := h.sp
  simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  omega

theorem Ctx.al {s t : State} (h : Pre s) (hc : Ctx s t) {d : Nat} (hd : d % 8 = 0) (hd' : d + 8 ≤ 32) :
    (t.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 d).toNat % 8 = 0 := al8 h hc.sp hd hd'

/-- The link register and the arguments saved, and the digest's arguments. -/
theorem saveArgs_ok {s : State} (h : Pre s) :
    WP isa (.block saveArgs) (allocd 32 s) fun t => Ctx s t ∧ t.gpr .a0 = s.gpr .a2 ∧
      t.gpr .a1 = BitVec.ofNat 64 32 ∧ t.gpr .a2 = s.gpr .a1 := by
  have e0 : (allocd 32 s).sp = K s + BitVec.ofNat 64 448 := sp32 s
  have ew : (allocd 32 s).wr = AR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 32, 32⟩ : Region) :: s.wr = _
    rw [sp32]
  have em : (allocd 32 s).mem = s.mem := rfl
  have eg : (allocd 32 s).gpr = s.gpr := rfl
  have er : (allocd 32 s).rd = s.rd := rfl
  have esy : (allocd 32 s).syms = s.syms := rfl
  generalize allocd 32 s = u at e0 ew em eg er esy
  have ha : ∀ d, u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 d = K s + BitVec.ofNat 64 (448 + d) := fun d => by
    simp only [e0, add_add, Nat.add_zero]
  have hin : ∀ d, d + 8 ≤ 32 → InRegions u.wr (u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [ew, ha]
    exact ⟨AR s, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩
  have hal : ∀ d, d % 8 = 0 → d + 8 ≤ 32 → (u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 d).toNat % 8 = 0 :=
    fun _ hd hd' => al8 h e0 hd hd'
  refine Steps.WP.cons (exec_addSp0 _) ?_
  refine Steps.WP.cons (exec_store_d (t := .ra) (n := .t0) (off := 0) (by decide) (hal 0 (by decide) (by decide))
    (hin 0 (by decide))) ?_
  refine Steps.WP.cons (exec_store_d (t := .a0) (n := .t0) (off := 8) (by decide) (hal 8 (by decide) (by decide))
    (hin 8 (by decide))) ?_
  refine Steps.WP.cons (exec_store_d (t := .a1) (n := .t0) (off := 16) (by decide) (hal 16 (by decide) (by decide))
    (hin 16 (by decide))) ?_
  refine Steps.WP.cons (exec_store_d (t := .a3) (n := .t0) (off := 24) (by decide) (hal 24 (by decide) (by decide))
    (hin 24 (by decide))) ?_
  refine Steps.WP.cons (exec_addi (d := .a0) (n := .a2) (imm := 0) (by decide)) ?_
  refine Steps.WP.cons (exec_addi (d := .a2) (n := .a1) (imm := 0) (by decide)) ?_
  refine Steps.WP.cons (exec_li (d := .a1) (imm := 32) (by decide)) (WP.block_nil_iff.mpr ?_)
  have hk : STK s ∈ [OUT s, EXP s, SCR s, STK s] := by simp
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ 480 → e + 8 ≤ 480 →
      Mem.Sep (K s + BitVec.ofNat 64 d) (64 / 8) (K s + BitVec.ofNat 64 e) (64 / 8) :=
    fun h₁ h₂ h₃ => Offset.sep _ h₁ (by omega) (by omega)
  have kc : ∀ {d : Nat}, d + 8 ≤ 480 → (STK s).Contains (K s + BitVec.ofNat 64 d) 8 :=
    fun hd => Offset.contains_base _ hd (by omega)
  -- The memory, and the registers, after the block.
  refine (?_ : ∀ t : State, t.rd = u.rd → t.wr = u.wr → t.sp = u.sp → t.syms = u.syms →
      (∀ r ∈ preserved, t.gpr r = u.gpr r) → t.gpr .a0 = u.gpr .a2 + BitVec.ofInt 64 0 →
      t.gpr .a1 = BitVec.ofInt 64 32 → t.gpr .a2 = u.gpr .a1 + BitVec.ofInt 64 0 →
      t.mem = ((((u.mem.writeW (u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0) (u.gpr .ra)).writeW
        (u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (u.gpr .a0)).writeW
        (u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 16) (u.gpr .a1)).writeW
        (u.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 24) (u.gpr .a3)) →
      Ctx s t ∧ t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a1 = BitVec.ofNat 64 32 ∧ t.gpr .a2 = s.gpr .a1)
    _ rfl rfl rfl rfl (fun r hr => by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl rfl
  intro t trd twr tsp tsy tcs t3 t4 t5 tm
  rw [ha, ha, ha, ha, em] at tm
  have z : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := rfl
  rw [z, BitVec.add_zero] at t3 t5
  refine ⟨⟨trd.trans er, twr.trans ew, tsp.trans e0, fun r hr => (tcs r hr).trans (congrFun eg r), ?_, ?_, ?_, ?_,
    tsy.trans esy, ?_⟩, by rw [t3, eg], t4.trans rfl, by rw [t5, eg]⟩
  · rw [tm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64, eg]
  · rw [tm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64, eg]
  · rw [tm, Mem.readW_writeW_sep (sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64,
      eg]
  · rw [tm, Mem.readW_writeW_self64, eg]
  · rw [tm]
    exact ((((Frame.refl _ _).writeW hk _ (kc (by decide))).writeW hk _ (kc (by decide))).writeW hk _
      (kc (by decide))).writeW hk _ (kc (by decide))

/-! ## Memory -/

/-- Bytes outside the regions a frame lists are kept. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' p n = Spec.Ed25519.bytesAt m p n :=
  List.map_congr_left fun _ hi => Frame.bytes hf (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem Ctx.bytes {s t : State} (hc : Ctx s t) {p : Addr} {n : Nat}
    (h₁ : Region.Disjoint ⟨p, n⟩ (OUT s)) (h₂ : Region.Disjoint ⟨p, n⟩ (EXP s))
    (h₃ : Region.Disjoint ⟨p, n⟩ (SCR s)) (h₄ : Region.Disjoint ⟨p, n⟩ (STK s)) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem p n = Spec.Ed25519.bytesAt s.mem p n := by
  refine bytesAt_frame hc.frame (fun r hr => ?_) hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- The `n` bytes below `sp`, from within the frame. -/
theorem Ctx.belowEq {s t : State} (hc : Ctx s t) {n : Nat} (hn : n ≤ 448) :
    below t.sp n = ⟨K s + BitVec.ofNat 64 (448 - n), n⟩ := by
  show (⟨t.sp - BitVec.ofNat 64 n, n⟩ : Region) = _
  rw [hc.sp, off_sub _ hn]

/-- After a call from within the frame that writes `wr` (within `out`,
`expanded` and `scratch`) and `n` bytes below `sp`, `Ctx` holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {n : Nat}
    (hn : n ≤ 448) (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hf : Frame (wr ++ [below t.sp n]) t.mem t'.mem)
    (hcs : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hsy : t'.syms = t.syms) : Ctx s t' := by
  rw [hc.belowEq hn] at hf
  have keep : ∀ e, 448 ≤ e → e + 8 ≤ 480 →
      t'.mem.readW (K s + BitVec.ofNat 64 e) 64 = t.mem.readW (K s + BitVec.ofNat 64 e) 64 := by
    intro e h₁ h₂
    refine hf.readW (r := ⟨K s + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rcases hsub r hr with rfl | rfl | rfl
      · exact h.kO (by omega)
      · exact h.kE (by omega)
      · exact h.kC (by omega)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr => (hcs r hr).trans (hc.cs r hr),
    (keep 448 (by decide) (by decide)).trans hc.ra, (keep 456 (by decide) (by decide)).trans hc.fOut,
    (keep 464 (by decide) (by decide)).trans hc.fExp, (keep 472 (by decide) (by decide)).trans hc.fScr,
    hsy.trans hc.sym, hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, stk_sub s (by omega)⟩

/-! ## The digest -/

abbrev dgCode : Prog isa := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512.hash

abbrev dgK : Contract isa := Spec.Sha512.digestContract RISCV64.abi 64 Spec.Sha512.sha512 448

theorem dg_verified : Verified RISCV64.target dgCode dgK := Proof.Hmac.Stream.RISCV64.Sha512.digest

theorem dg_stack : sdepth dgCode = 448 := by decide +kernel

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx3 : t.gpr .a0 = s.gpr .a2)
    (hx4 : t.gpr .a1 = BitVec.ofNat 64 32) (hx5 : t.gpr .a2 = s.gpr .a1) :
    dgK.pre (t.callEntry.withRegions [SEED s] [EXP s]) := by
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, RISCV64.abi,
    RISCV64.argRegs, stackBelow]
  have hb := hc.belowEq (n := 448) (Nat.le_refl _)
  simp only [below] at hb
  rw [hx3, hx4, hx5, hb, show (BitVec.ofNat 64 32).toNat = 32 from rfl]
  refine ⟨hc.sp16 h, by rw [hc.sp, K_toNat h (by decide)]; omega, rfl, rfl, h.es.symm, ?_, ?_, h.ns, h.ne⟩
  · exact h.kS (by decide)
  · exact h.kE (by decide)

theorem dg_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers ([SEED s] ++ [EXP s]) (t.rd ++ t.wr) ∧ Covers [EXP s] t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp

/-- The digest's call: the seed's digest at `expanded`. -/
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (hx3 : t.gpr .a0 = s.gpr .a2)
    (hx4 : t.gpr .a1 = BitVec.ofNat 64 32) (hx5 : t.gpr .a2 = s.gpr .a1) :
    WP isa (.call dn dgCode) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .a1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32) := by
  refine WP.of_syms (WP.callAny dg_verified.1 (dg_pre h hc hx3 hx4 hx5) (dg_cov h hc).1 (dg_cov h hc).2
    (fun t' hrd hwr hsp hf hcs hpost hsy => ⟨?_, ?_⟩))
  · rw [dg_stack] at hf
    exact Ctx.call h hc (by decide) (by simp) hrd hwr hsp hf hcs hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, RISCV64.abi,
      RISCV64.argRegs] at hpost
    rw [hx3, hx4, hx5, show (BitVec.ofNat 64 32).toNat = 32 from rfl] at hpost
    have hS : Spec.Ed25519.bytesAt t.mem (s.gpr .a2) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32 :=
      hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

/-- The public key's arguments, from the frame. -/
theorem pkArgs_ok {s t : State} (h : Pre s) (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .a0 = s.gpr .a0 ∧
      t'.gpr .a1 = s.gpr .a1 ∧ t'.gpr .a2 = s.gpr .a3 := by
  have ld : ∀ d, t.mem.readW (t.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 d) 64 =
      t.mem.readW (K s + BitVec.ofNat 64 (448 + d)) 64 := fun d => by
    simp only [hc.sp, add_add, Nat.add_zero]
  refine Steps.WP.cons (exec_addSp0 _) ?_
  refine Steps.WP.cons (exec_load_d (t := .a0) (n := .t0) (off := 8) (by decide) (hc.al h (d := 8) (by decide) (by decide))
    (hc.inAR (d := 8) (by decide))) ?_
  refine Steps.WP.cons (exec_load_d (t := .a1) (n := .t0) (off := 16) (by decide) (hc.al h (d := 16) (by decide) (by decide))
    (hc.inAR (d := 16) (by decide))) ?_
  refine Steps.WP.cons (exec_load_d (t := .a2) (n := .t0) (off := 24) (by decide) (hc.al h (d := 24) (by decide) (by decide))
    (hc.inAR (d := 24) (by decide))) (WP.block_nil_iff.mpr
      ⟨(((hc.write (by decide) _).write (by decide) _).write (by decide) _).write (by decide) _, rfl, ?_, ?_, ?_⟩)
  · rw [RegUpd.gpr_write_of_ne (h := (show ¬Reg.a0 = Reg.a2 by decide)),
      RegUpd.gpr_write_of_ne (h := (show ¬Reg.a0 = Reg.a1 by decide)), RegUpd.gpr_write_self]
    exact (ld 8).trans hc.fOut
  · rw [RegUpd.gpr_write_of_ne (h := (show ¬Reg.a1 = Reg.a2 by decide)), RegUpd.gpr_write_self]
    exact (ld 16).trans hc.fExp
  · rw [RegUpd.gpr_write_self]
    exact (ld 24).trans hc.fScr

abbrev pkCode : Prog isa := Impl.Ed25519.RISCV64.Whole.publicKeyExpandedCode

abbrev pkK : Contract isa := Spec.Ed25519.publicKeyExpandedContract (RISCV64.abi.withConsts combConsts) 352

theorem pk_verified : Verified RISCV64.target pkCode pkK := Proof.Ed25519.RISCV64.Whole.publicKeyExpanded_framed

theorem pk_stack : sdepth pkCode = 144 := by decide +kernel

abbrev pkRd (s : State) : List Region := [EXP s, TB s]
abbrev pkWr (s : State) : List Region := [OUT s, SCR s]

theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx3 : t.gpr .a0 = s.gpr .a0)
    (hx4 : t.gpr .a1 = s.gpr .a1) (hx5 : t.gpr .a2 = s.gpr .a3)
    (hE : Spec.Ed25519.bytesAt t.mem (s.gpr .a1) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32)) :
    pkK.pre (t.callEntry.withRegions (pkRd s) (pkWr s)) := by
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, RISCV64.abi, RISCV64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  have hb := hc.belowEq (n := 352) (by decide)
  simp only [below] at hb
  rw [hx3, hx4, hx5, hb, hc.sym]
  have hT : ∀ r ∈ [OUT s, EXP s, SCR s, STK s], (TB s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tO
    · exact h.tE
    · exact h.tC
    · exact h.tK
  refine ⟨hc.sp16 h, by rw [hc.sp, K_toNat h (by decide)]; omega, rfl, fun i hi => ?_, h.fit, h.tO, h.tC,
    h.kT (by decide),
    h.al, rfl, rfl, h.oe, h.oc, h.ec, h.kO (by decide), h.kE (by decide), h.kC (by decide), h.no, h.ne, h.nc.1,
    ⟨_, by simp [Spec.Ed25519.bytesAt], hE⟩, h.nc.2⟩
  exact (hc.frame.readW (r := TB s) (a := s.syms combSym + BitVec.ofNat 64 (8 * i)) (w := 64)
    (Offset.contains_base _ (show 8 * i + 64 / 8 ≤ 8 * combWords.length by omega)
      (by have := h.fit; omega)) hT (by decide)).trans (h.held i hi)

theorem pk_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers (pkRd s ++ pkWr s) (t.rd ++ t.wr) ∧ Covers (pkWr s) t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The public key's call: the seed's public key at `out`, the digest kept. -/
theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (hx3 : t.gpr .a0 = s.gpr .a0)
    (hx4 : t.gpr .a1 = s.gpr .a1) (hx5 : t.gpr .a2 = s.gpr .a3)
    (hE : Spec.Ed25519.bytesAt t.mem (s.gpr .a1) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32)) :
    WP isa (.call pn pkCode) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .a1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32) ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .a0) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32) := by
  refine WP.of_syms (WP.callAny pk_verified.1 (pk_pre h hc hx3 hx4 hx5 hE) (pk_cov h hc).1 (pk_cov h hc).2
    (fun t' hrd hwr hsp hf hcs hpost hsy => ?_))
  rw [pk_stack] at hf
  refine ⟨Ctx.call h hc (by decide) (by simp) hrd hwr hsp hf hcs hsy, ?_, ?_⟩
  · rw [← hE]
    rw [hc.belowEq (by decide)] at hf
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · exact (h.kE (by decide)).symm
  · sig_post [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, RISCV64.abi, RISCV64.argRegs, combConsts_eq, Abi.withConsts] at hpost
    rw [hx3, hx4] at hpost
    exact hpost _ (by simp [Spec.Ed25519.bytesAt]) hE

/-! ## The link register, and the whole function -/

theorem restore_ok {s t : State} (h : Pre s) (hc : Ctx s t) :
    WP isa (.block restoreRa) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧ t'.mem = t.mem ∧
      (∀ r ∈ preserved, t'.gpr r = s.gpr r) ∧ t'.gpr .ra = s.gpr .ra := by
  refine Steps.WP.cons (exec_addSp0 _) ?_
  refine Steps.WP.cons (exec_load_d (t := .ra) (n := .t0) (off := 0) (by decide) (hc.al h (d := 0) (by decide) (by decide))
    (hc.inAR (d := 0) (by decide))) (WP.block_nil_iff.mpr ⟨rfl, rfl, rfl, rfl, fun r hr => ?_, ?_⟩)
  · have h0 : ¬r = .ra := by rintro rfl; revert hr; decide
    have h12 : ¬r = .t0 := by rintro rfl; revert hr; decide
    rw [RegUpd.gpr_write_of_ne (h := h0), RegUpd.gpr_write_of_ne (h := h12)]; exact hc.cs r hr
  · rw [RegUpd.gpr_write_self]
    show t.mem.readW (t.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 0) 64 = _
    rw [hc.sp, add_add, add_add]; exact hc.ra

/-- The body, from the frame's push. -/
theorem body_ok {s : State} (h : Pre s) {dn pn : String} :
    WP isa (.seq (.block saveArgs) (.seq (.call dn dgCode) (.seq (.block pkArgs) (.seq (.call pn pkCode)
      (.block restoreRa))))) (allocd 32 s) fun u => u.sp = K s + BitVec.ofNat 64 448 ∧
      (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.gpr .ra = s.gpr .ra ∧
      Spec.Ed25519.bytesAt u.mem (s.gpr .a1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32) ∧
      Spec.Ed25519.bytesAt u.mem (s.gpr .a0) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32) := by
  refine WP.seq (WP.mono (saveArgs_ok h) fun t ⟨hc, hx3, hx4, hx5⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok h hc hx3 hx4 hx5) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok h hc) fun t' ⟨hc', hm, hx3, hx4, hx5⟩ => ?_)
  refine WP.seq (WP.mono (pk_ok h hc' hx3 hx4 hx5 (by rw [hm]; exact hE)) fun u ⟨hu, hE', hO⟩ => ?_)
  exact WP.mono (restore_ok h hu) fun _ ⟨_, _, hsp, hm, hcs, hlr⟩ =>
    ⟨hsp.trans hu.sp, hcs, hlr, by rw [hm]; exact hE', by rw [hm]; exact hO⟩

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn dgCode pn pkCode) s fun s' => abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  refine WP.alloc (by decide) (by have := h.sp; omega) (WP.mono (body_ok h) fun u ⟨hsp, hcs, hlr, hE, hO⟩ =>
    ⟨⟨hcs, ?_, hlr⟩, ?_⟩)
  · show u.sp + BitVec.ofNat 64 32 = s.sp
    rw [hsp, add_add, sp_eq s]
  · sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, RISCV64.abi,
      RISCV64.argRegs, combConsts_eq, Abi.withConsts]
    exact ⟨hE, hO⟩

/-! ## Constant time -/

structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  a0 : s₁.gpr .a0 = s₂.gpr .a0
  a1 : s₁.gpr .a1 = s₂.gpr .a1
  a2 : s₁.gpr .a2 = s₂.gpr .a2
  a3 : s₁.gpr .a3 = s₂.gpr .a3
  sy : s₁.syms combSym = s₂.syms combSym

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, combConsts_eq, Abi.withConsts] at h
  obtain ⟨h0, hs, h1, h2, h3, h4⟩ := h
  exact ⟨h0, h1, h2, h3, h4, hs⟩

def Rel (Φ : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ Ctx s₁ a ∧ Ctx s₂ b ∧ Φ s₁ a ∧ Φ s₂ b

theorem rel_wp {c : Prog isa} {Φ Ψ : State → State → Prop} (hct : RelCT isa (Rel Φ) c fun _ _ => True)
    (hw : ∀ s t, Pre s → Ctx s t → Φ s t → WP isa c t fun t' => Ctx s t' ∧ Ψ s t') :
    RelCT isa (Rel Φ) c (Rel Ψ) := by
  intro a b ta tb a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, h₁, h₂, hp', c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ a h₁ c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ b h₂ c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem rel_sp {Φ : State → State → Prop} {a b : State} (h : Rel Φ a b) : a.sp = b.sp := by
  obtain ⟨_, _, _, _, hp, c₁, c₂, _⟩ := h
  rw [c₁.sp, c₂.sp, K, K, hp.sp]

/-- A block whose addresses depend only on the stack pointer. -/
theorem block_ct {is : List Instr} {P : State → State → Prop} (hsp : ∀ a b, P a b → a.sp = b.sp)
    {hint : VG.Taint.Hint taint.T}
    (hc : (taint.check (RISCV64.Taint.ofRegs []) (.block is) hint).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  (RelCT.taint (A := taint) (RISCV64.Taint.ofRegs []) (fun a b h => ⟨hsp a b h, fun r hr => by
    simp only [RISCV64.Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) hc).mono (fun _ _ h => h) fun _ _ _ => trivial

abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a1 = BitVec.ofNat 64 32 ∧ t.gpr .a2 = s.gpr .a1
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .a0 = s.gpr .a0 ∧ t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = s.gpr .a3

abbrev Entered (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = allocd 32 s₁ ∧ b = allocd 32 s₂

theorem body_ct {dn pn : String} :
    RelCT isa Entered (.seq (.block saveArgs) (.seq (.call dn dgCode) (.seq (.block pkArgs)
      (.seq (.call pn pkCode) (.block restoreRa))))) fun _ _ => True := by
  have b₁ : RelCT isa Entered (.block saveArgs) (Rel Φ₁) := by
    intro a b ta tb a' b' hp e₁ e₂
    obtain ⟨ht, -⟩ := block_ct (fun a b (hp : Entered a b) => by
      obtain ⟨s₁, s₂, -, -, hp, rfl, rfl⟩ := hp
      show s₁.sp - BitVec.ofNat 64 32 = s₂.sp - BitVec.ofNat 64 32
      rw [hp.sp]) (by taint_decide) _ _ _ _ _ _ hp e₁ e₂
    obtain ⟨s₁, s₂, h₁, h₂, hp', rfl, rfl⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := saveArgs_ok h₁
    obtain ⟨_, u₂, x₂, y₂⟩ := saveArgs_ok h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2⟩
  have b₂ : RelCT isa (Rel Φ₁) (.call dn dgCode) (Rel Φ₂) := by
    refine rel_wp (RelCT.callEx dg_verified.1 dg_verified.2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hx3, hx4, hx5⟩ => digest_ok h hc hx3 hx4 hx5
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨d₁, i₁, x₁⟩, ⟨d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, dg_pre h₁ c₁ d₁ i₁ x₁, dg_pre h₂ c₂ d₂ i₂ x₂, ?_, (dg_cov h₁ c₁).1, (dg_cov h₁ c₁).2,
      (dg_cov h₂ c₂).1, (dg_cov h₂ c₂).2⟩
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, RISCV64.abi,
      RISCV64.argRegs]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, K, K, hp.sp, hp.a2, hp.a1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have b₃ : RelCT isa (Rel Φ₂) (.block pkArgs) (Rel Φ₃) :=
    rel_wp (block_ct (fun _ _ hr => rel_sp hr) (by taint_decide)) fun _ _ h hc hE =>
      WP.mono (pkArgs_ok h hc) fun _ ⟨hc', hm, a, b, d⟩ => ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel Φ₃) (.call pn pkCode) (Rel fun _ _ => True) := by
    refine rel_wp (RelCT.callEx pk_verified.1 pk_verified.2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hE, hx3, hx4, hx5⟩ => WP.mono (pk_ok h hc hx3 hx4 hx5 hE) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨e₁, d₁, i₁, x₁⟩, ⟨e₂, d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, pk_pre h₁ c₁ d₁ i₁ x₁ e₁, pk_pre h₂ c₂ d₂ i₂ x₂ e₂, ?_, (pk_cov h₁ c₁).1,
      (pk_cov h₁ c₁).2, (pk_cov h₂ c₂).1, (pk_cov h₂ c₂).2⟩
    sig_pub [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, RISCV64.abi, RISCV64.argRegs, combConsts_eq, Abi.withConsts]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, c₁.sym, c₂.sym, K, K, hp.sp, hp.a0, hp.a1, hp.a3, hp.sy]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have b₅ : RelCT isa (Rel fun _ _ => True) (.block restoreRa) fun _ _ => True :=
    block_ct (fun _ _ hr => rel_sp hr) (by taint_decide)
  exact b₁.seq (b₂.seq (b₃.seq (b₄.seq b₅)))

/-- A frame of local variables leaks what its body does. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨by simp only [addrs], trivial⟩

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn dgCode pn pkCode) := by
  refine RelCT.constantTime (alloc_ct (RelCT.mono body_ct ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, pre_of h₁, pre_of h₂, pub_of hp, rfl, rfl⟩

/-! ## A witness, and the artifact's obligation -/

/-- A state satisfying the precondition: `out` at `0x1000`, `expanded` at `0x2000`, the seed at
`0x3000`, `scratch` at `0x4000`, the stack below `0x9000` and the comb's tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x9000
  mem := Proof.Ed25519.RISCV64.Whole.satMemTE
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem sat_pre : Pre satState := by
  have hl := Proof.Ed25519.RISCV64.combWords_length
  refine ⟨by decide, by decide, by simp only [satState, SEED, TB, hl], rfl,
    Proof.Ed25519.RISCV64.Whole.satMemTE_held,
    by simp only [satState, hl]; decide, by decide,
    by simp only [TB, OUT, satState, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, EXP, satState, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, SCR, satState, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, STK, satState, hl]; exact Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩

theorem verified {dn pn : String} :
    Verified RISCV64.target (keyPair dn dgCode pn pkCode) spec :=
  ⟨fun _ h => keyPair_ok h, keyPair_ct, ⟨_, spec_of sat_pre⟩⟩

end VG.Proof.Ed25519.RISCV64.KeyPair
