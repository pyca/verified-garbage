module

public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.AArch64.KeyPair
public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Expanded
public import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Impl.Ed25519.AArch64.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Expanded
meta import VerifiedGarbage.Proof.Sha512.AArch64.OneShot
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT

/-!
# Ed25519 key-pair derivation on AArch64

`keyPair` calls the one-shot SHA-512 digest of an implementation `v` of the
compression function, which writes the seed's digest to `expanded`, and then
`vg_ed25519_public_key_expanded`, which derives the public key from it. Its
proof uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`sp - 944` on entry): `x30` is saved at `K s + 928`, the
allocation is at `K s + 896` (`out`, `expanded` and `scratch` in its first
three words), and both calls enter with `sp = K s + 896`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.KeyPair

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.KeyPair
open VG.Proof.Ed25519.AArch64 (TBL CombHeld)

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (AArch64.abi.withConsts combConsts) 944

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := s.sp - BitVec.ofNat 64 944

abbrev OUT (s : State) : Region := ⟨s.gpr .x0, 32⟩
abbrev EXP (s : State) : Region := ⟨s.gpr .x1, 64⟩
abbrev SEED (s : State) : Region := ⟨s.gpr .x2, 32⟩
abbrev SCR (s : State) : Region := ⟨s.gpr .x3, 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 944⟩
abbrev TB (s : State) : Region := ⟨s.syms combSym, 8 * combWords.length⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 944 ≤ s.sp.toNat
  rd : s.rd = [SEED s, TB s]
  wr : s.wr = [OUT s, EXP s, SCR s]
  held : ∀ i < combWords.length,
    s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0
  fit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64
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
  no : (s.gpr .x0).toNat + 32 ≤ 2 ^ 64
  ne : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64
  ns : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64
  nc : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨hsp, hd, hheld, hfit, hdw, hdk, -, ht, hw, oe, os, oc, es, ec, sc,
    ko, ke, ks, kc, no, ne, ns, nc⟩ := h
  refine ⟨hsp, ?_, hw, hheld, hfit, hdw _ (by rw [hw]; simp), hdw _ (by rw [hw]; simp),
    hdw _ (by rw [hw]; simp), hdk, oe, os, oc, es, ec, sc, ko, ke, ks, kc, no, ne, ns, nc⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl

/-- The precondition, from its facts and the tables' alignment. -/
theorem spec_of {s : State} (h : Pre s) (hal : (s.syms combSym).toNat % 64 = 0) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  refine ⟨h.sp, by rw [h.rd]; rfl, h.held, h.fit, fun r hr => ?_, h.tK, hal, by rw [h.rd]; rfl, h.wr,
    h.oe, h.os, h.oc, h.es, h.ec, h.sc, h.ko, h.ke, h.ks, h.kc, h.no, h.ne, h.ns, h.nc⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.tO
  · exact h.tE
  · exact h.tC

/-! ## Addresses on the stack -/

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a - BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a - b) := by
  have : b < 2 ^ 64 := by omega
  have : a - b < 2 ^ 64 := by omega
  bv_omega

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sp_eq (s : State) : s.sp = K s + BitVec.ofNat 64 944 := by
  simp only [K, BitVec.sub_add_cancel]

theorem sp16 (s : State) : s.sp - 16 = K s + BitVec.ofNat 64 928 := by
  rw [sp_eq s]; exact off_sub _ (b := 16) (by decide) (by decide)

theorem sp48 (s : State) : s.sp - 16 - BitVec.ofNat 64 32 = K s + BitVec.ofNat 64 896 := by
  rw [sp16 s]; exact off_sub _ (by decide) (by decide)

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 944) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

theorem K_toNat {s : State} (h : Pre s) {d : Nat} (hd : d ≤ 944) :
    (K s + BitVec.ofNat 64 d).toNat = (K s).toNat + d := by
  have hk : (K s).toNat + 944 = s.sp.toNat := by
    have := h.sp
    simp only [K, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have := s.sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 944) : Region.Disjoint (TB s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  h.tK.sub_right (stk_sub s hd)

end Pre

/-! ## Between the frame's allocation and its release -/

/-- The allocation. -/
abbrev AL (s : State) : Region := ⟨K s + BitVec.ofNat 64 896, 32⟩
/-- Where `x30` is saved. -/
abbrev LR (s : State) : Region := ⟨K s + BitVec.ofNat 64 928, 16⟩

/-- What holds after the arguments are saved, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = AL s :: LR s :: s.wr
  sp : t.sp = K s + BitVec.ofNat 64 896
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  lr : t.mem.read (K s + BitVec.ofNat 64 928) 8 = s.gpr .x30
  fOut : t.mem.read (K s + BitVec.ofNat 64 896) 8 = s.gpr .x0
  fExp : t.mem.read (K s + BitVec.ofNat 64 904) 8 = s.gpr .x1
  fScr : t.mem.read (K s + BitVec.ofNat 64 912) 8 = s.gpr .x3
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

/-- The state the body starts in. -/
abbrev entered (s : State) : State := allocated 32 (pushed .x30 s)

theorem entered_sp (s : State) : (entered s).sp = K s + BitVec.ofNat 64 896 := sp48 s

theorem entered_wr (s : State) : (entered s).wr = AL s :: LR s :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 32, 32⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [sp48, sp16]

theorem entered_in {s : State} {d : Nat} (hd : d + 8 ≤ 32) :
    InRegions (entered s).wr ((entered s).sp + BitVec.ofNat 64 d) 8 := by
  rw [entered_wr, entered_sp, add_add]
  exact ⟨AL s, List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- The arguments saved, and the digest's arguments. -/
theorem digestArgs_ok (s : State) :
    WP isa (.block digestArgs) (entered s) fun t => Ctx s t ∧ t.gpr .x0 = s.gpr .x2 ∧
      t.gpr .x1 = BitVec.ofNat 64 32 ∧ t.gpr .x2 = s.gpr .x1 := by
  have h0 : InRegions (entered s).wr (entered s).sp 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using entered_in (s := s) (d := 0) (by decide)
  have h8 := entered_in (s := s) (d := 8) (by decide)
  have h16 := entered_in (s := s) (d := 16) (by decide)
  apply WP.of_runBlock
  have hz : (BitVec.ofNat 16 32).setWidth 64 <<< 0 = BitVec.ofNat 64 32 := by decide
  simp only [digestArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.store, State.read,
    h0, h8, h16, ite_true, Nat.reduceMod, Nat.reduceLT, and_self, Size.bits, BitVec.setWidth_eq,
    BitVec.add_zero, Nat.mul_zero, Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self,
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x1 = Reg.x0 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x2 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x1 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x2 = Reg.x1 by decide))]
  have e0 : (entered s).gpr = s.gpr := rfl
  have em : (entered s).mem = s.mem.write (K s + BitVec.ofNat 64 928) 8 (s.gpr .x30) := by
    show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _; rw [sp16]
  rw [e0, em, entered_sp, add_add, add_add]
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ 944 → e + 8 ≤ 944 →
      Mem.Sep (K s + BitVec.ofNat 64 d) 8 (K s + BitVec.ofNat 64 e) 8 :=
    fun h₁ h₂ h₃ => Offset.sep _ h₁ (by omega) (by omega)
  have kc : ∀ {d : Nat}, d + 8 ≤ 944 → (STK s).Contains (K s + BitVec.ofNat 64 d) 8 :=
    fun hd => Offset.contains_base _ hd (by omega)
  have hk : STK s ∈ [OUT s, EXP s, SCR s, STK s] := by simp
  refine ⟨⟨rfl, entered_wr s, rfl, fun r hr hr' => ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_, rfl,
    (((((Frame.refl _ _).write hk _ (kc (by decide))).write hk _ (kc (by decide))).write hk _
      (kc (by decide))).write hk _ (kc (by decide)))⟩, rfl, hz, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hr' | rfl
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide), read_write_self]
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide),
      Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide), read_write_self]
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [Mem.read_write_sep (sep (by decide) (by decide) (by decide)) (by decide), read_write_self]
  · show Mem.read (Mem.write _ _ 8 _) _ 8 = _
    rw [read_write_self]

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

/-- What a call from the frame may change below `sp`, `16 d` bytes: within the stack used. -/
theorem below_sub {s t : State} (hc : Ctx s t) {d : Nat} (hd : 16 * d ≤ 896) :
    Region.Sub (below t.sp (16 * d)) (STK s) := by
  rw [hc.sp]
  show Region.Sub ⟨K s + BitVec.ofNat 64 896 - BitVec.ofNat 64 (16 * d), 16 * d⟩ _
  rw [off_sub _ hd (by decide)]
  exact stk_sub s (by omega)

/-- After a call from the frame that writes `wr` (within `out`, `expanded` and
`scratch`) and the stack below `sp` the callee uses, `Ctx` holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {d : Nat}
    (hd : 16 * d ≤ 896) (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hf : Frame (wr ++ [below t.sp (16 * d)]) t.mem t'.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hsy : t'.syms = t.syms) : Ctx s t' := by
  have keep : ∀ e, 896 ≤ e → e + 8 ≤ 944 →
      t'.mem.read (K s + BitVec.ofNat 64 e) 8 = t.mem.read (K s + BitVec.ofNat 64 e) 8 := by
    intro e h₁ h₂
    refine hf.read (r := ⟨K s + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rcases hsub r hr with rfl | rfl | rfl
      · exact h.kO (by omega)
      · exact h.kE (by omega)
      · exact h.kC (by omega)
    · rw [List.mem_singleton.mp hr, hc.sp]
      have e' : K s + BitVec.ofNat 64 e = K s + BitVec.ofNat 64 896 + BitVec.ofNat 64 (e - 896) := by
        rw [add_add, Nat.add_sub_cancel' h₁]
      rw [e']
      exact Offset.disjoint_below _ (by omega)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    (keep 928 (by decide) (by decide)).trans hc.lr, (keep 896 (by decide) (by decide)).trans hc.fOut,
    (keep 904 (by decide) (by decide)).trans hc.fExp, (keep 912 (by decide) (by decide)).trans hc.fScr,
    hsy.trans hc.sym, hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, below_sub hc hd⟩

/-! ## The digest -/

variable (v : Proof.Sha512.AArch64.Compress)

abbrev dgCode : Prog isa :=
  Proof.Sha512.AArch64.oneShotWith (Impl.MdStream.AArch64.out64 8) Spec.Sha512.H0_512 v.suffix v.code

abbrev dgK : Contract isa :=
  Spec.Sha512.digestContract AArch64.abi 64 Spec.Sha512.sha512 Proof.Sha512.AArch64.OneShot.stack

theorem dg_verified : Verified AArch64.target (dgCode v) dgK :=
  (v.oneShot_verified (by decide) Proof.Sha512.AArch64.Stream.shape.toD v.oneShot512).of_implies
    (Proof.Sha512.AArch64.OneShot.implies (by decide) fun m =>
      List.take_of_length_le (Nat.le_of_eq (VG.Proof.Hmac.Generic.Common.finalHash_length _ m)))

theorem dg_depth : (dgCode v).aarch64Depth ≤ 56 := by
  have h0 := Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames v.noFrames
  simp only [Proof.Sha512.AArch64.oneShotWith, Impl.MdStream.AArch64.OneShot.digest,
    Impl.MdStream.AArch64.OneShot.body, Impl.MdStream.AArch64.OneShot.whole,
    Impl.MdStream.AArch64.OneShot.tail, Impl.MdStream.AArch64.OneShot.compressWith,
    Impl.MdStream.AArch64.OneShot.compressBuf, Impl.MdStream.AArch64.OneShot.copyTail,
    Impl.MdStream.AArch64.OneShot.bytesTail, Impl.Sha512.AArch64.Stream.initPairs,
    Code.aarch64Depth, h0, Proof.Sha512.AArch64.OneShot.frameBytes_out, Nat.max_self,
    AArch64.Instr.frameUnits, Nat.zero_add]
  decide

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := State.callEntry_gpr t h

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .x0 = s.gpr .x2)
    (hx1 : t.gpr .x1 = BitVec.ofNat 64 32) (hx2 : t.gpr .x2 = s.gpr .x1) :
    dgK.pre (t.callEntry.withRegions [SEED s] [EXP s]) := by
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
    AArch64.argRegs, stackBelow]
  rw [hc.sp, hx0, hx1, hx2, BitVec.add_sub_cancel, show (BitVec.ofNat 64 32).toNat = 32 from rfl]
  have k0 : ∀ {n}, (⟨K s, n⟩ : Region) = ⟨K s + BitVec.ofNat 64 0, n⟩ := by simp
  refine ⟨by rw [K_toNat h (by decide)]; show 896 ≤ _; omega, rfl, rfl, h.es.symm, ?_, ?_, h.ns, h.ne⟩
  · rw [k0]; exact h.kS (by decide)
  · rw [k0]; exact h.kE (by decide)

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
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (hx0 : t.gpr .x0 = s.gpr .x2)
    (hx1 : t.gpr .x1 = BitVec.ofNat 64 32) (hx2 : t.gpr .x2 = s.gpr .x1) :
    WP isa (.call dn (dgCode v)) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .x1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) := by
  have hd := dg_depth v
  refine WP.of_syms (WP.callFV (dg_verified v).1 (dg_pre h hc hx0 hx1 hx2) (dg_cov h hc).1 (dg_cov h hc).2
    (fun t' hrd hwr hsp hf hcs hvs hpost hsy => ⟨?_, ?_⟩) (by omega))
  · exact Ctx.call h hc (by omega) (by simp) hrd hwr hsp hf hcs hvs hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs] at hpost
    simp only [hx0, hx1, hx2, show (BitVec.ofNat 64 32).toNat = 32 from rfl] at hpost
    have hS : Spec.Ed25519.bytesAt t.mem (s.gpr .x2) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32 :=
      hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

/-- A write of a register the ABI does not preserve. -/
theorem Ctx.write {s t : State} (hc : Ctx s t) {r : Reg} (hr : r ∉ preserved) (x : BitVec 64) :
    Ctx s (t.write .x r x) :=
  ⟨hc.rd, hc.wr, hc.sp, fun q hq hq' => by
      have hne : ¬q = r := fun e => hr (e ▸ hq)
      rw [RegUpd.gpr_write_of_ne (h := hne)]; exact hc.cs q hq hq',
    hc.vs, hc.lr, hc.fOut, hc.fExp, hc.fScr, hc.sym, hc.frame⟩

/-- The public key's arguments, from the allocation. -/
theorem pkArgs_ok {s t : State} (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .x0 = s.gpr .x0 ∧
      t'.gpr .x1 = s.gpr .x1 ∧ t'.gpr .x2 = s.gpr .x3 := by
  have hin : ∀ d, d + 8 ≤ 32 → InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hc.wr, hc.sp, add_add]
    exact ⟨AL s, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩
  have h0 : InRegions (t.rd ++ t.wr) t.sp 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hin 0 (by decide)
  have h8 := hin 8 (by decide)
  have h16 := hin 16 (by decide)
  apply WP.of_runBlock
  simp only [pkArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, h0, h8, h16, ite_true,
    Nat.reduceMod, Nat.reduceLT, and_self, Option.map_some, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', RegUpd.sp_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x1 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x0 = Reg.x2 by decide)),
    RegUpd.gpr_write_of_ne (h := (show ¬Reg.x1 = Reg.x2 by decide))]
  have e0 : t.sp = K s + BitVec.ofNat 64 896 := hc.sp
  rw [e0, add_add, add_add]
  exact ⟨((hc.write (by decide) _).write (by decide) _).write (by decide) _, trivial, hc.fOut, hc.fExp,
    hc.fScr⟩

abbrev pkRd (s : State) : List Region := [EXP s, TB s]
abbrev pkWr (s : State) : List Region := [OUT s, SCR s]

theorem pk_depth : PublicKey.codeExpanded.aarch64Depth ≤ 22 := by
  have h := PublicKey.bodyE_depth
  simp only [PublicKey.codeExpanded, Impl.Ed25519.AArch64.Whole.wrap, Code.aarch64Depth,
    AArch64.Instr.frameUnits, Nat.zero_max]
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

theorem ce_syms (t : State) (rd wr : List Region) : (t.callEntry.withRegions rd wr).syms = t.syms := rfl

theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .x0 = s.gpr .x0)
    (hx1 : t.gpr .x1 = s.gpr .x1) (hx2 : t.gpr .x2 = s.gpr .x3) :
    PublicKey.pkLocalE.pre (t.callEntry.withRegions (pkRd s) (pkWr s)) := by
  simp only [PublicKey.pkLocalE, Proof.Ed25519.AArch64.PublicKey.pkLocalWith, CombHeld,
    ce_gpr t _ _ (show Reg.x0 ∉ linkRegs by decide), ce_gpr t _ _ (show Reg.x1 ∉ linkRegs by decide),
    ce_gpr t _ _ (show Reg.x2 ∉ linkRegs by decide), State.withRegions_sp, State.callEntry_sp,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, hc.sp, hx0, hx1,
    hx2, ce_syms, hc.sym, below]
  rw [off_sub _ (b := 352) (by decide) (by decide)]
  refine ⟨trivial, trivial, h.oe, h.oc, h.ec, h.kO (by decide), h.kE (by decide), h.kC (by decide), h.no, h.ne, h.nc,
    by rw [K_toNat h (by decide)]; omega, fun i hi => ?_, h.fit, fun r hr => ?_⟩
  · rw [hc.frame.readW (r := TB s) (Offset.contains_base _ (by have := h.fit; omega) (by have := h.fit; omega))
      (fun r hr => ?_) (by decide)]
    · exact h.held i hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.tO
      · exact h.tE
      · exact h.tC
      · exact h.tK
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.tO
    · exact h.tC
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

section
variable [Proof.Ed25519.AArch64.Divstep.Sound]

theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (hx0 : t.gpr .x0 = s.gpr .x0)
    (hx1 : t.gpr .x1 = s.gpr .x1) (hx2 : t.gpr .x2 = s.gpr .x3)
    (hE : Spec.Ed25519.bytesAt t.mem (s.gpr .x1) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32)) :
    WP isa (.call pn PublicKey.codeExpanded) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .x1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) ∧
      Spec.Ed25519.bytesAt t'.mem (s.gpr .x0) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) := by
  have hd := pk_depth
  refine WP.of_syms (WP.callFV (k := PublicKey.pkLocalE) (fun _ h => PublicKey.pkE_ok h)
    (pk_pre h hc hx0 hx1 hx2) (pk_cov h hc).1 (pk_cov h hc).2
    (fun t' hrd hwr hsp hf hcs hvs hpost hsy =>
      ⟨Ctx.call h hc (by omega) (by simp) hrd hwr hsp hf hcs hvs hsy, ?_, ?_⟩) (by omega))
  · rw [← hE]
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · exact h.ke.symm.sub_right (below_sub hc (by omega))
  · simp only [PublicKey.pkLocalE, Proof.Ed25519.AArch64.PublicKey.pkLocalWith, State.withRegions_mem,
      State.callEntry_mem, ce_gpr t _ _ (show Reg.x0 ∉ linkRegs by decide),
      ce_gpr t _ _ (show Reg.x1 ∉ linkRegs by decide), hx0, hx1] at hpost
    exact hpost _ (by simp [Spec.Ed25519.bytesAt]) hE

/-! ## The whole function -/

/-- The frame's body, from the allocation. -/
theorem body_ok {s : State} (h : Pre s) {dn pn : String} :
    WP isa (.seq (.block digestArgs) (.seq (.call dn (dgCode v)) (.seq (.block pkArgs)
      (.call pn PublicKey.codeExpanded)))) (entered s) fun t => Ctx s t ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .x1) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32) := by
  refine WP.seq (WP.mono (digestArgs_ok s) fun t ⟨hc, hx0, hx1, hx2⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok v h hc hx0 hx1 hx2) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok hc) fun t' ⟨hc', hm, hx0, hx1, hx2⟩ => ?_)
  exact pk_ok h hc' hx0 hx1 hx2 (by rw [hm]; exact hE)

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn (dgCode v) pn PublicKey.codeExpanded) s fun s' =>
      abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  have hsp := h.sp
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ (WP.mono (body_ok v h) fun u ⟨hu, hE, hO⟩ => ⟨?_, ?_⟩))
  · show 32 ≤ (s.sp - 16).toNat
    rw [sp16, K_toNat h (by decide)]; omega
  · have hsp' : (freed 32 u).sp = K s + BitVec.ofNat 64 928 := by
      show u.sp + BitVec.ofNat 64 32 = _; rw [hu.sp, add_add]
    refine ⟨fun r hr => ?_, ?_, fun r hr => hu.vs r hr⟩
    · by_cases h30 : r = .x30
      · subst h30
        show ((freed 32 u).mem.read (freed 32 u).sp 8).setWidth 64 = _
        rw [hsp', BitVec.setWidth_eq]; exact hu.lr
      · show (if r = .x30 then _ else u.gpr r) = _
        rw [ite_eq_right_iff.mpr (fun h => absurd h h30)]; exact hu.cs r hr h30
    · show (freed 32 u).sp + 16 = s.sp
      rw [hsp', sp_eq s]; exact add_add _ _ _
  · sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    exact ⟨hE, hO⟩

end

/-! ## Constant time -/

structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  sy : s₁.syms combSym = s₂.syms combSym

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
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

variable [Proof.Ed25519.AArch64.Divstep.Sound]

abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .x0 = s.gpr .x2 ∧ t.gpr .x1 = BitVec.ofNat 64 32 ∧ t.gpr .x2 = s.gpr .x1
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (s.gpr .x1) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x3

theorem body_ct {dn pn : String} :
    RelCT isa (fun a b => ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂)
      (.seq (.block digestArgs) (.seq (.call dn (dgCode v)) (.seq (.block pkArgs)
        (.call pn PublicKey.codeExpanded)))) fun _ _ => True := by
  have b₁ : RelCT isa (fun a b => ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂)
      (.block digestArgs) (Rel Φ₁) := by
    intro a b ta tb a' b' hp e₁ e₂
    obtain ⟨ht, -⟩ := Whole.block_rel (P := fun a b => ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧
        a = entered s₁ ∧ b = entered s₂)
      (fun _ _ ⟨s₁, s₂, _, _, hp, ea, eb⟩ => by rw [ea, eb, entered_sp, entered_sp, K, K, hp.sp])
      (by taint_decide) _ _ _ _ _ _ hp e₁ e₂
    obtain ⟨s₁, s₂, h₁, h₂, hp', rfl, rfl⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := digestArgs_ok s₁
    obtain ⟨_, u₂, x₂, y₂⟩ := digestArgs_ok s₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2⟩
  have b₂ : RelCT isa (Rel Φ₁) (.call dn (dgCode v)) (Rel Φ₂) := by
    refine rel_wp (RelCT.callEx (dg_verified v).1 (dg_verified v).2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hx0, hx1, hx2⟩ => digest_ok v h hc hx0 hx1 hx2
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨d₁, i₁, x₁⟩, ⟨d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, dg_pre h₁ c₁ d₁ i₁ x₁, dg_pre h₂ c₂ d₂ i₂ x₂, ?_, (dg_cov h₁ c₁).1, (dg_cov h₁ c₁).2,
      (dg_cov h₂ c₂).1, (dg_cov h₂ c₂).2⟩
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, AArch64.abi,
      AArch64.argRegs]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, K, K, hp.sp, hp.x2, hp.x1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have b₃ : RelCT isa (Rel Φ₂) (.block pkArgs) (Rel Φ₃) :=
    rel_wp (Whole.block_rel (fun _ _ hr => rel_sp hr) (by taint_decide)) fun _ _ _ hc hE =>
      WP.mono (pkArgs_ok hc) fun _ ⟨hc', hm, a, b, d⟩ => ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel Φ₃) (.call pn PublicKey.codeExpanded) fun _ _ => True := by
    refine RelCT.callEx (k := PublicKey.pkLocalE) (fun _ h => PublicKey.pkE_ok h) PublicKey.pkE_ct
      fun a b hr => ?_
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨-, d₁, i₁, x₁⟩, ⟨-, d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, pk_pre h₁ c₁ d₁ i₁ x₁, pk_pre h₂ c₂ d₂ i₂ x₂, ?_, (pk_cov h₁ c₁).1,
      (pk_cov h₁ c₁).2, (pk_cov h₂ c₂).1, (pk_cov h₂ c₂).2⟩
    simp only [PublicKey.pkLocalE, Proof.Ed25519.AArch64.PublicKey.pkLocalWith, State.withRegions_sp,
      State.callEntry_sp, ce_syms, ce_gpr _ _ _ (show Reg.x0 ∉ linkRegs by decide),
      ce_gpr _ _ _ (show Reg.x1 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.x2 ∉ linkRegs by decide),
      c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, c₁.sym, c₂.sym, K, hp.sp, hp.x0, hp.x1, hp.x3, hp.sy]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  exact b₁.seq (b₂.seq (b₃.seq b₄))

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn (dgCode v) pn PublicKey.codeExpanded) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => (pub_of h.2.2).sp)
    (RelCT.alloc (RelCT.mono (body_ct v) ?_ fun _ _ _ => trivial)))
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, pre_of h₁, pre_of h₂, pub_of hp, rfl, rfl⟩

/-! ## A witness, and the artifact's obligation -/

/-- A state satisfying the precondition: `out` at `0x1000`, `expanded` at `0x2000`, the seed at
`0x3000`, `scratch` at `0x4000`, the stack below `0x9000` and the comb's tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x9000
  mem := PublicKey.satMemTE
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 49152⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

omit [Proof.Ed25519.AArch64.Divstep.Sound] in
theorem sat_pre : Pre satState := by
  have hl := combWords_length
  refine ⟨by decide, by simp only [satState, SEED, TB, hl], rfl, PublicKey.satMemTE_held,
    by simp only [satState, hl]; decide,
    by simp only [TB, OUT, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, EXP, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, SCR, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, STK, hl]; exact Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩

omit [Proof.Ed25519.AArch64.Divstep.Sound] in
theorem sat : spec.pre satState := spec_of sat_pre (by decide)

theorem verified {dn pn : String} :
    Verified AArch64.target (keyPair dn (dgCode v) pn PublicKey.codeExpanded) spec :=
  ⟨fun _ h => keyPair_ok v h, keyPair_ct v, ⟨_, sat⟩⟩

end VG.Proof.Ed25519.AArch64.KeyPair
