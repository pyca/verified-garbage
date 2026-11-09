module

public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.X86_64.KeyPair
public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Expanded
public import VerifiedGarbage.Proof.Sha512.X86_64.OneShot
public import VerifiedGarbage.Proof.Sha512.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Impl.Ed25519.X86_64.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Expanded
meta import VerifiedGarbage.Proof.Sha512.X86_64.OneShot
meta import VerifiedGarbage.Proof.Sha512.X86_64.Variant
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-!
# Ed25519 key-pair derivation on x86-64

`keyPair` calls the one-shot SHA-512 digest of an implementation `c` of the
compression function, which writes the seed's digest to `expanded`, and then
`vg_ed25519_public_key_expanded` with the base-point multiplication `bs`,
which derives the public key from it (`publicKeyExpandedContract`). Its proof
uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`rsp - 1632` on entry): the frame is at `K s + 1608`,
`scratch`, `expanded` and `out` in that order, and both calls enter with
`rsp = K s + 1600`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.KeyPair

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.KeyPair
open VG.Proof.Ed25519.X86_64 (combRegion CombHeld)
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add)

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (X86_64.abi.withConsts combConsts) 1632

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 1632

abbrev OUT (s : State) : Region := ⟨s.gpr .rdi, 32⟩
abbrev EXP (s : State) : Region := ⟨s.gpr .rsi, 64⟩
abbrev SEED (s : State) : Region := ⟨s.gpr .rdx, 32⟩
abbrev SCR (s : State) : Region := ⟨s.gpr .rcx, 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 1632⟩
abbrev TBL (s : State) : Region := combRegion (s.syms combSym)

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 1632 ≤ (s.gpr .rsp).toNat
  rd : s.rd = [SEED s, TBL s]
  wr : s.wr = [OUT s, EXP s, SCR s]
  held : CombHeld s [OUT s, EXP s, SCR s, ⟨s.gpr .rsp, 8⟩, STK s]
  oe : (OUT s).Disjoint (EXP s)
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  es : (EXP s).Disjoint (SEED s)
  ec : (EXP s).Disjoint (SCR s)
  sc : (SEED s).Disjoint (SCR s)
  ro : Region.Disjoint ⟨s.gpr .rsp, 8⟩ (OUT s)
  re : Region.Disjoint ⟨s.gpr .rsp, 8⟩ (EXP s)
  rs : Region.Disjoint ⟨s.gpr .rsp, 8⟩ (SEED s)
  rc : Region.Disjoint ⟨s.gpr .rsp, 8⟩ (SCR s)
  ko : (STK s).Disjoint (OUT s)
  ke : (STK s).Disjoint (EXP s)
  ks : (STK s).Disjoint (SEED s)
  kc : (STK s).Disjoint (SCR s)
  no : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64
  ne : (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64
  ns : (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64
  nc : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    Proof.Ed25519.X86_64.combWords_length] at h
  obtain ⟨hsp, hd, hheld, hfit, hdw, hdr, hdk, -, ht, hw, oe, os, oc, es, ec, sc, ro, re, rs, rc,
    ko, ke, ks, kc, no, ne, ns, nc⟩ := h
  refine ⟨hsp, ?_, hw, ⟨hheld, hfit, fun r hr => ?_⟩, oe, os, oc, es, ec, sc, ro, re, rs, rc,
    ko, ke, ks, kc, no, ne, ns, nc⟩
  · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hdw _ (by rw [hw]; simp)
    · exact hdw _ (by rw [hw]; simp)
    · exact hdw _ (by rw [hw]; simp)
    · exact hdr
    · exact hdk

/-! ## Addresses on the stack -/

theorem sp_sub (s : State) {n : Nat} (h : n ≤ 1632) :
    s.gpr .rsp - BitVec.ofNat 64 n = K s + BitVec.ofNat 64 (1632 - n) := by
  have : 1632 - n < 2 ^ 64 := by omega
  bv_omega

theorem sp_eq (s : State) : s.gpr .rsp = K s + BitVec.ofNat 64 1632 := by
  simp only [K, BitVec.sub_add_cancel]

/-- The frame's base, after the push. -/
abbrev B (s : State) : Addr := K s + BitVec.ofNat 64 1608

/-- A range of the stack used is in it. -/
theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 1632) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 1632) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 1632) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 1632) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 1632) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 1632) : Region.Disjoint (TBL s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  (h.held.2.2 (STK s) (by simp)).sub_right (stk_sub s hd)
theorem tO (h : Pre s) : (TBL s).Disjoint (OUT s) := h.held.2.2 _ (by simp)
theorem tE (h : Pre s) : (TBL s).Disjoint (EXP s) := h.held.2.2 _ (by simp)
theorem tC (h : Pre s) : (TBL s).Disjoint (SCR s) := h.held.2.2 _ (by simp)
end Pre

/-! ## Between the frame's push and pop -/

/-- What holds between the push and the pop, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨B s, 24⟩ :: s.wr
  rsp : t.gpr .rsp = B s
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fOut : t.mem.readW (B s + BitVec.ofNat 64 16) 64 = s.gpr .rdi
  fExp : t.mem.readW (B s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  fScr : t.mem.readW (B s + BitVec.ofNat 64 0) 64 = s.gpr .rcx
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

theorem push_ctx {s : State} (h : Pre s) : Ctx s (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 24 ≤ _; have := h.sp; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have e : s.gpr .rsp - BitVec.ofNat 64 (8 * pushRs.length) = B s := by
    show s.gpr .rsp - BitVec.ofNat 64 24 = _; rw [sp_sub s (by decide)]
  have slot : ∀ j (hj : j < 3), (pushed pushRs s).mem.readW (B s + BitVec.ofNat 64 (16 - 8 * j)) 64 =
      s.gpr (pushRs[j]'(by simp only [pushRs, List.length_cons, List.length_nil]; omega)) := fun j hj => by
    have ha : B s + BitVec.ofNat 64 (16 - 8 * j) = s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [sp_sub s (by omega), add_add]; congr 2; omega
    show (pushRegs s pushRs).mem.readW _ 64 = _
    rw [ha]; exact hw j _
  refine ⟨by rw [pushed_rd], by rw [pushed_wr, e]; rfl, by rw [pushed_rsp, e], fun r _ hr => pushed_gpr _ _ hr,
    by rw [pushed_mxcsr], slot 0 (by decide), slot 1 (by decide), slot 2 (by decide),
    pushRegs_syms s pushRs, Frame.sub hf fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨STK s, by simp, ?_⟩
  rw [e]
  exact stk_sub s (by decide)

namespace Ctx

variable {s t t' : State}

/-- Code that changes only caller-saved registers. -/
theorem regs (hc : Ctx s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hsy : t'.syms = t.syms) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) :
    Ctx s t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.fOut, by rw [hm]; exact hc.fExp, by rw [hm]; exact hc.fScr,
    by rw [hsy]; exact hc.sym, by rw [hm]; exact hc.frame⟩

end Ctx

/-- The digest's arguments. -/
theorem digestArgs_ok {s t : State} (hc : Ctx s t) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hsi : t.gpr .rsi = s.gpr .rsi) :
    WP isa (.block digestArgs) t fun t' => Ctx s t' ∧ t'.gpr .rdi = s.gpr .rdx ∧
      t'.gpr .rsi = BitVec.ofNat 64 32 ∧ t'.gpr .rdx = s.gpr .rsi := by
  apply WP.of_runBlock
  simp only [digestArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true,
    Option.some.injEq, exists_eq_left', hdx, hsi]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, by decide, trivial⟩

/-! ## Memory -/

/-- Bytes outside the regions a frame lists are kept. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' p n = Spec.Ed25519.bytesAt m p n :=
  List.map_congr_left fun _ hi => Frame.bytes hf (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The entry state's bytes in a region apart from what the frame lets change. -/
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

/-- A region apart from a call's return address keeps its bytes on entry to the callee. -/
theorem bytesAt_ce (t : State) {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨p, n⟩ (below (t.gpr .rsp) 8))
    (hn : n ≤ 2 ^ 64) : Spec.Ed25519.bytesAt t.callEntry.mem p n = Spec.Ed25519.bytesAt t.mem p n := by
  refine bytesAt_frame (rs := [below (t.gpr .rsp) 8]) ?_ (by simpa using hd) hn
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-! ## The digest -/

variable (c : Proof.Sha512.X86_64.Compress)

/-- The one-shot SHA-512 digest with `c`. -/
abbrev dgCode : Prog isa :=
  Proof.Sha512.X86_64.OneShot.digest (Impl.MdStream.X86_64.out64 8) Spec.Sha512.H0_512 c.callee

abbrev dgK : Contract isa := Spec.Sha512.digestContract X86_64.abi 64 Spec.Sha512.sha512 1600

theorem dg_verified : Verified X86_64.target (dgCode c) dgK :=
  Proof.Sha512.X86_64.OneShot.verified Proof.Sha512.X86_64.OneShot.code512
    (fun _ => List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _)))
    c.ok c.mxcsr c.spSafe c.noStack

theorem dg_all : (dgCode c).all (fun i => !isa.writesSp i) = true :=
  Proof.Sha512.X86_64.OneShot.spSafe Proof.Sha512.X86_64.OneShot.code512 Spec.Sha512.H0_512 c.spSafe

theorem dg_depth : (dgCode c).x86_64Depth ≤ 1600 := by
  show (Impl.StackScratch.X86_64.withStackScratch (Impl.MdStream.X86_64.OneShot.frameBytes _) .rcx
    (Proof.Sha512.X86_64.OneShot.body _ _ c.callee)).x86_64Depth ≤ 1600
  rw [Proof.Sha512.X86_64.OneShot.frameBytes_eq]
  have hb : (Proof.Sha512.X86_64.OneShot.body (Impl.MdStream.X86_64.out64 8) Spec.Sha512.H0_512
      c.callee).x86_64Depth ≤ 8 := by
    rw [Proof.MdStream.X86_64.OneShot.body_depth _
      (rfl : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).x86_64Depth = 0)]
    exact Proof.Sha512.X86_64.OneShot.code512.depth c.callee c.noStack
  simp only [Impl.StackScratch.X86_64.withStackScratch, Code.x86_64Depth]
  show max 0 _ + 1592 ≤ 1600
  simp only [Nat.zero_max]
  exact Nat.add_le_add_right hb 1592

/-! ## The calls' stack -/

theorem B_toNat {s : State} (h : Pre s) {d : Nat} (hd : d ≤ 1632) :
    (K s + BitVec.ofNat 64 d).toNat = (K s).toNat + d := by
  have hk : (K s).toNat + 1632 = (s.gpr .rsp).toNat := by
    have := h.sp
    simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have := (s.gpr .rsp).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The entry `rsp` of a call from the frame. -/
theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a - BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a - b) := by
  have : b < 2 ^ 64 := by omega
  have : a - b < 2 ^ 64 := by omega
  bv_omega

theorem rsp8 {s t : State} (hc : Ctx s t) : t.gpr .rsp - 8 = K s + BitVec.ofNat 64 1600 := by
  rw [hc.rsp]
  exact off_sub _ (b := 8) (by decide) (by decide)

theorem ce_rsp {s t : State} (hc : Ctx s t) : t.callEntry.gpr .rsp = K s + BitVec.ofNat 64 1600 := by
  rw [State.callEntry_rsp, rsp8 hc]

/-- The return address of a call from the frame. -/
theorem ret_eq {s t : State} (hc : Ctx s t) : below (t.gpr .rsp) 8 = ⟨K s + BitVec.ofNat 64 1600, 8⟩ := by
  simp only [below, hc.rsp]
  rw [off_sub _ (by decide) (by decide)]

/-- What a call from the frame may change below `rsp`, `d + 8` bytes: within the stack used. -/
theorem below_sub {s t : State} (hc : Ctx s t) {d : Nat} (hd : d ≤ 1600) :
    Region.Sub (below (t.gpr .rsp) (d + 8)) (STK s) := by
  rw [hc.rsp]
  have e : K s + BitVec.ofNat 64 1608 - BitVec.ofNat 64 (d + 8) = K s + BitVec.ofNat 64 (1600 - d) := by
    rw [off_sub _ (by omega) (by omega)]; congr 2; omega
  show Region.Sub ⟨K s + BitVec.ofNat 64 1608 - BitVec.ofNat 64 (d + 8), d + 8⟩ _
  rw [e]
  exact stk_sub s (by omega)

/-- The frame's slots are apart from what a call from it may change below `rsp`. -/
theorem slot_below {s t : State} (hc : Ctx s t) {j n : Nat} (hj : j + 8 ≤ 24) (hn : n ≤ 1632) :
    Region.Disjoint ⟨B s + BitVec.ofNat 64 j, 8⟩ (below (t.gpr .rsp) n) := by
  rw [hc.rsp]
  exact Offset.disjoint_below _ (by omega)

/-- The frame's slot `j` survives a call that writes only `wr`, apart from it, and below `rsp`. -/
theorem slot_keep {s t t' : State} (hc : Ctx s t) {wr : List Region} {n j : Nat} (hj : j + 8 ≤ 24) (hn : n ≤ 1632)
    (hf : Frame (wr ++ [below (t.gpr .rsp) n]) t.mem t'.mem)
    (hw : ∀ r ∈ wr, Region.Disjoint ⟨B s + BitVec.ofNat 64 j, 8⟩ r) :
    t'.mem.readW (B s + BitVec.ofNat 64 j) 64 = t.mem.readW (B s + BitVec.ofNat 64 j) 64 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r hr
  · rw [List.mem_singleton.mp hr]; exact slot_below hc hj hn

/-- After a call from the frame that writes `wr` (within `out`, `expanded` and
`scratch`) and the stack below `rsp` the callee uses, `Ctx` holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {d : Nat} (hd : d ≤ 1600)
    (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame (wr ++ [below (t.gpr .rsp) (d + 8)]) t.mem t'.mem)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) (hsy : t'.syms = t.syms) : Ctx s t' := by
  have hw : ∀ j, j + 8 ≤ 24 → ∀ r ∈ wr, Region.Disjoint ⟨B s + BitVec.ofNat 64 j, 8⟩ r := by
    intro j hj r hr
    have e : B s + BitVec.ofNat 64 j = K s + BitVec.ofNat 64 (1608 + j) := add_add _ _ _
    rw [e]
    rcases hsub r hr with rfl | rfl | rfl
    · exact h.kO (by omega)
    · exact h.kE (by omega)
    · exact h.kC (by omega)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hcs .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hmx.trans hc.mx,
    (slot_keep hc (by decide) (by omega) hf (hw 16 (by decide))).trans hc.fOut,
    (slot_keep hc (by decide) (by omega) hf (hw 8 (by decide))).trans hc.fExp,
    (slot_keep hc (by decide) (by omega) hf (hw 0 (by decide))).trans hc.fScr, hsy.trans hc.sym,
    hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, below_sub hc hd⟩

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hdi : t.gpr .rdi = s.gpr .rdx)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 32) (hdx : t.gpr .rdx = s.gpr .rsi) :
    dgK.pre (t.callEntry.withRegions [SEED s] [EXP s]) := by
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, X86_64.abi,
    X86_64.argRegs, stackBelow]
  rw [rsp8 hc, hdi, hsi, hdx, BitVec.add_sub_cancel, show (BitVec.ofNat 64 32).toNat = 32 from rfl]
  exact ⟨by rw [B_toNat h (by decide)]; omega, rfl, rfl, h.es.symm, h.kS (by decide), h.kE (by decide),
    by simpa using h.kS (d := 0) (n := 1600) (by decide), by simpa using h.kE (d := 0) (n := 1600) (by decide),
    h.ns, h.ne⟩

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
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (hdi : t.gpr .rdi = s.gpr .rdx)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 32) (hdx : t.gpr .rdx = s.gpr .rsi) :
    WP isa (.call dn (dgCode c)) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .rsi) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32) := by
  refine WP.of_syms (WP.callF (dg_verified c).1 (SpSafe.of_all (dg_all c)) (by have := dg_depth c; omega)
    (dg_pre h hc hdi hsi hdx) (dg_cov h hc).1 (dg_cov h hc).2
    fun t' hrd hwr hcs hf ⟨s₂, hm₂, _, hpost⟩ hmx hsy => ⟨?_, ?_⟩)
  · exact Ctx.call h hc (dg_depth c) (by simp) hrd hwr hcs hf hmx hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, X86_64.abi,
      X86_64.argRegs] at hpost
    rw [hdi, hsi, hdx, hm₂, show (BitVec.ofNat 64 32).toNat = 32 from rfl] at hpost
    have hS : Spec.Ed25519.bytesAt t.callEntry.mem (s.gpr .rdx) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32 := by
      rw [bytesAt_ce t (by rw [ret_eq hc]; exact (h.kS (by decide)).symm) (by decide)]
      exact hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

/-- The public key's arguments, from the frame. -/
theorem pkArgs_ok {s t : State} (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧
      t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rcx := by
  have hin : ∀ d, d + 8 ≤ 24 → InRegions (t.rd ++ t.wr) (B s + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨⟨B s, 24⟩, by rw [hc.wr]; simp, Offset.contains_base _ hd (by omega)⟩
  have h16 := hin 16 (by decide)
  have h8 := hin 8 (by decide)
  have h0 := hin 0 (by decide)
  apply WP.of_runBlock
  simp only [pkArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hc.rsp, h16, h8, h0,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', hc.fOut, hc.fExp, hc.fScr,
    reduceCtorEq, ite_false]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

variable (bs : Prog isa) [Proof.Ed25519.X86_64.EdBase bs] (fs : String)

theorem pk_depth : (publicKeyExpanded bs fs).x86_64Depth ≤ 72 := by
  have h := x86_64Depth_noSp (PublicKey.base_nosp (bs := bs))
  have hd := PublicKey.base_depth (bs := bs)
  simp only [publicKeyExpanded, pkBodyFrom, pkCopyExpanded, Code.x86_64Depth, h]
  show max 0 (max 0 (max 0 (max (8 * bs.depth + 8) 0))) + 56 ≤ 72
  simp only [Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hd) 8) 56

/-- The comb's tables, in memory that changed only apart from them. -/
theorem held_of {s : State} (h : Pre s) {rs : List Region} {m : Mem} (hf : Frame rs s.mem m)
    (hd : ∀ r ∈ rs, (TBL s).Disjoint r) :
    ∀ i < combWordCount, m.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  have hn := h.held.2.1
  rw [hf.readW (r := TBL s) (Offset.contains_base _ (by simp only [combWordCount] at *; omega_arith)
    (by simp only [combWordCount] at *; omega_arith)) hd (by decide)]
  exact h.held.1 i hi

/-- The regions of the public key's call. -/
abbrev pkRd (s : State) : List Region := [EXP s, TBL s]
abbrev pkWr (s : State) : List Region := [OUT s, SCR s]

theorem ce_syms (t : State) (rd wr : List Region) : (t.callEntry.withRegions rd wr).syms = t.syms := rfl

/-- The public key's precondition, after `pkArgs`, with the seed's digest at `expanded`. -/
theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rcx)
    (hE : Spec.Ed25519.bytesAt t.mem (s.gpr .rsi) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32)) :
    PublicKey.pkLocalE.pre (t.callEntry.withRegions (pkRd s) (pkWr s)) := by
  simp only [PublicKey.pkLocalE, PublicKey.pkLocalWith, CombHeld, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_mem, ce_syms, ce_rsp hc,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), hdi, hsi, hdx, hc.sym]
  rw [off_sub _ (b := 72) (by decide) (by decide)]
  have hret : Frame [⟨K s + BitVec.ofNat 64 1600, 8⟩] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, ← ret_eq hc]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hm : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.callEntry.mem :=
    hc.frame.trans (hret.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨STK s, by simp, stk_sub s (by decide)⟩)
  refine ⟨by rw [B_toNat h (by decide)]; omega, trivial, trivial, h.oe, h.oc, h.ec,
    (h.kO (by decide)), (h.kE (by decide)), (h.kC (by decide)),
    (h.kO (by decide)), (h.kE (by decide)), (h.kC (by decide)), h.no, h.ne, h.nc,
    ⟨Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32, PublicKey.bytesAt_length _ _ _, ?_⟩,
    held_of h hm fun r hr => ?_, h.held.2.1, fun r hr => ?_⟩
  · rw [bytesAt_ce t (by rw [ret_eq hc]; exact (h.kE (by decide)).symm) (by decide)]
    exact hE
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tO
    · exact h.tE
    · exact h.tC
    · exact h.held.2.2 _ (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tO
    · exact h.tC
    · exact h.kT (by decide)
    · exact h.kT (by decide)

theorem pk_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers (pkRd s ++ pkWr s) (t.rd ++ t.wr) ∧ Covers (pkWr s) t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rcx)
    (hE : Spec.Ed25519.bytesAt t.mem (s.gpr .rsi) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32)) :
    WP isa (.call pn (publicKeyExpanded bs fs)) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .rsi) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32) ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .rdi) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32) := by
  have hd := pk_depth bs fs
  refine WP.of_syms (WP.callF (k := PublicKey.pkLocalE)
    (fun _ h => PublicKey.publicKeyExpanded_ok (bs := bs) (fs := fs) h)
    (SpSafe.of_all PublicKey.publicKeyExpanded_spSafe) (by omega) (pk_pre h hc hdi hsi hdx hE)
    (pk_cov h hc).1 (pk_cov h hc).2
    fun t' hrd hwr hcs hf ⟨s₂, hm₂, _, hpost⟩ hmx hsy =>
      ⟨Ctx.call h hc (by omega) (by simp) hrd hwr hcs hf hmx hsy, ?_, ?_⟩)
  · rw [← hE]
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · exact h.ke.symm.sub_right (below_sub hc (by omega))
  · simp only [PublicKey.pkLocalE, PublicKey.pkLocalWith, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      hdi, hsi, hm₂] at hpost
    refine hpost _ (PublicKey.bytesAt_length _ _ _) ?_
    rw [bytesAt_ce t (by rw [ret_eq hc]; exact (h.kE (by decide)).symm) (by decide)]
    exact hE

/-! ## The whole function -/

/-- The frame's body, from the push. -/
theorem body_ok {s : State} (h : Pre s) {dn pn : String} :
    WP isa (.seq (.block digestArgs) (.seq (.call dn (dgCode c)) (.seq (.block pkArgs)
      (.call pn (publicKeyExpanded bs fs))))) (pushed pushRs s) fun t => Ctx s t ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .rsi) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32) ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .rdi) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32) := by
  refine WP.seq (WP.mono (digestArgs_ok (push_ctx h) (pushed_gpr _ _ (by decide))
    (pushed_gpr _ _ (by decide))) fun t ⟨hc, hdi, hsi, hdx⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok c h hc hdi hsi hdx) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok hc) fun t' ⟨hc', hm, hdi, hsi, hdx⟩ => ?_)
  exact pk_ok bs fs h hc' hdi hsi hdx (by rw [hm]; exact hE)

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn (dgCode c) pn (publicKeyExpanded bs fs)) s fun s' =>
      abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  have hc₀ := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide)
    (by show 24 ≤ _; have := h.sp; omega)
    (WP.mono (body_ok c bs fs h) fun u ⟨hu, hE, hO⟩ => ⟨hu.rsp.trans hc₀.rsp.symm, hu.wr.trans hc₀.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, sp_eq s]
      exact add_add _ _ _
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (PublicKey.ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.ro
      · exact h.re
      · exact h.rc
      · rw [sp_eq s]; exact Offset.disjoint_base _ (by decide) (by decide)
  · sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
      X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq, Abi.withConsts]
    exact ⟨hE, hO⟩

/-! ## Constant time -/

/-- What two runs agree on. -/
structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.gpr .rsp = s₂.gpr .rsp
  di : s₁.gpr .rdi = s₂.gpr .rdi
  si : s₁.gpr .rsi = s₂.gpr .rsi
  dx : s₁.gpr .rdx = s₂.gpr .rdx
  cx : s₁.gpr .rcx = s₂.gpr .rcx
  sy : s₁.syms combSym = s₂.syms combSym

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
    X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq, Abi.withConsts] at h
  obtain ⟨h0, hs, h1, h2, h3, h4⟩ := h
  exact ⟨h0, h1, h2, h3, h4, hs⟩

/-- Two runs between the push and the pop, from entry states that agree, each with `Φ`. -/
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

theorem rel_rsp {Φ : State → State → Prop} {a b : State} (h : Rel Φ a b) : a.gpr .rsp = b.gpr .rsp := by
  obtain ⟨_, _, _, _, hp, c₁, c₂, _⟩ := h
  rw [c₁.rsp, c₂.rsp, B, B, K, K, hp.sp]

/-- A block that addresses memory only through `rsp`. -/
theorem rel_block {is : List Instr} {Φ Ψ : State → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ s t, Pre s → Ctx s t → Φ s t → WP isa (.block is) t fun t' => Ctx s t' ∧ Ψ s t') :
    RelCT isa (Rel Φ) (.block is) (Rel Ψ) :=
  rel_wp (RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ hr => Taint.agree_ofRegs fun r hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact rel_rsp hr) h) hw

abbrev Φ₀ (s t : State) : Prop := t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rsi = s.gpr .rsi
abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .rdi = s.gpr .rdx ∧ t.gpr .rsi = BitVec.ofNat 64 32 ∧ t.gpr .rdx = s.gpr .rsi
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (s.gpr .rsi) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rcx

theorem body_ct {dn pn : String} :
    RelCT isa (Rel Φ₀) (.seq (.block digestArgs) (.seq (.call dn (dgCode c)) (.seq (.block pkArgs)
      (.call pn (publicKeyExpanded bs fs))))) fun _ _ => True := by
  have b₁ : RelCT isa (Rel Φ₀) (.block digestArgs) (Rel Φ₁) :=
    rel_block (by taint_decide) fun _ _ _ hc ⟨hdx, hsi⟩ =>
      WP.mono (digestArgs_ok hc hdx hsi) fun _ ⟨hc', a, b, d⟩ => ⟨hc', a, b, d⟩
  have b₂ : RelCT isa (Rel Φ₁) (.call dn (dgCode c)) (Rel Φ₂) := by
    refine rel_wp (RelCT.callEx (dg_verified c).1 (dg_verified c).2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hdi, hsi, hdx⟩ => digest_ok c h hc hdi hsi hdx
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨d₁, i₁, x₁⟩, ⟨d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, dg_pre h₁ c₁ d₁ i₁ x₁, dg_pre h₂ c₂ d₂ i₂ x₂, ?_, (dg_cov h₁ c₁).1, (dg_cov h₁ c₁).2,
      (dg_cov h₂ c₂).1, (dg_cov h₂ c₂).2, rel_rsp (Φ := fun _ _ => True) ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, trivial, trivial⟩⟩
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, X86_64.abi,
      X86_64.argRegs]
    rw [rsp8 c₁, rsp8 c₂, d₁, d₂, i₁, i₂, x₁, x₂, K, K, hp.sp, hp.dx, hp.si]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have b₃ : RelCT isa (Rel Φ₂) (.block pkArgs) (Rel Φ₃) :=
    rel_block (by taint_decide) fun _ _ _ hc hE =>
      WP.mono (pkArgs_ok hc) fun _ ⟨hc', hm, a, b, d⟩ => ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel Φ₃) (.call pn (publicKeyExpanded bs fs)) fun _ _ => True := by
    refine RelCT.callEx (k := PublicKey.pkLocalE)
      (fun _ h => PublicKey.publicKeyExpanded_ok (bs := bs) (fs := fs) h)
      (PublicKey.publicKeyExpanded_ct (bs := bs) (fs := fs)) fun a b hr => ?_
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨e₁, d₁, i₁, x₁⟩, ⟨e₂, d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, pk_pre h₁ c₁ d₁ i₁ x₁ e₁, pk_pre h₂ c₂ d₂ i₂ x₂ e₂, ?_, (pk_cov h₁ c₁).1,
      (pk_cov h₁ c₁).2, (pk_cov h₂ c₂).1, (pk_cov h₂ c₂).2,
      rel_rsp (Φ := fun _ _ => True) ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, trivial, trivial⟩⟩
    simp only [PublicKey.pkLocalE, PublicKey.pkLocalWith, State.withRegions_gpr, ce_syms, ce_rsp c₁, ce_rsp c₂,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), d₁, d₂, i₁, i₂, x₁, x₂, c₁.sym, c₂.sym, K, hp.sp,
      hp.di, hp.si, hp.cx, hp.sy]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  exact b₁.seq (b₂.seq (b₃.seq b₄))

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn (dgCode c) pn (publicKeyExpanded bs fs)) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => (pub_of h.2.2).sp)
    (RelCT.mono (body_ct c bs fs) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, pre_of h₁, pre_of h₂, pub_of hp, push_ctx (pre_of h₁), push_ctx (pre_of h₂),
    ⟨pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide)⟩,
    ⟨pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide)⟩⟩

/-! ## A witness, and the artifact's obligations -/

/-- A state satisfying the precondition: `out` at `0x1000`, `expanded` at `0x2000`, the seed at
`0x3000`, `scratch` at `0x4000`, the stack below `0x8000` and the comb's tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := PublicKey.satMemPE
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 40448⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The precondition, from its facts and the tables' alignment. -/
theorem spec_of {s : State} (h : Pre s) (hal : (s.syms combSym).toNat % 64 = 0) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, Proof.Ed25519.X86_64.combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    Proof.Ed25519.X86_64.combWords_length]
  have hw := h.held.2.2
  refine ⟨h.sp, by rw [h.rd]; rfl, h.held.1, h.held.2.1, fun r hr => hw r (by
      rw [h.wr] at hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]),
    hw _ (by simp), hw _ (by simp), hal, by rw [h.rd]; rfl, h.wr, h.oe, h.os, h.oc, h.es, h.ec, h.sc,
    h.ro, h.re, h.rs, h.rc, h.ko, h.ke, h.ks, h.kc, h.no, h.ne, h.ns, h.nc⟩

theorem sat_pre : Pre satState := by
  refine ⟨by decide, rfl, rfl, ⟨PublicKey.satMemPE_held, by decide, ?_⟩, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem sat : spec.pre satState := spec_of sat_pre (by decide)

theorem verified {dn pn : String} :
    Verified X86_64.target (keyPair dn (dgCode c) pn (publicKeyExpanded bs fs)) spec :=
  ⟨fun _ h => keyPair_ok c bs fs h, keyPair_ct c bs fs, ⟨_, sat⟩⟩

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem spSafe {dn pn : String} :
    (keyPair dn (dgCode c) pn (publicKeyExpanded bs fs)).all (fun i => !isa.writesSp i) = true := by
  have h₁ := dg_all c
  have h₂ := PublicKey.publicKeyExpanded_spSafe (bs := bs) (fs := fs)
  rw [keyPair, Code.all, Code.all, Code.all, Code.all, Code.all, Code.all, Code.all, Code.all, h₁, h₂]
  decide

end VG.Proof.Ed25519.X86_64.KeyPair
