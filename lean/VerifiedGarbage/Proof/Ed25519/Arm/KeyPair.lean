module

public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.Arm.KeyPair
public import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Expanded
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT

/-!
# Ed25519 key-pair derivation on ARMv7

`keyPair` calls the one-shot SHA-512 digest (`vg_sha512_digest`), which
writes the seed's digest to `expanded`, and then
`vg_ed25519_public_key_expanded`, which derives the public key from it. Its
proof uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`sp - 600` on entry): `lr` is saved at `K s + 596`, `out`,
`expanded` and `scratch` at `K s + 584`, `+ 588` and `+ 592`, and both calls
enter with `sp` at `K s + 584`, the digest using the 584 bytes below it.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.KeyPair

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Ed25519.Arm VG.Impl.Ed25519.Arm.KeyPair

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (Arm.abi.withConsts combConsts) 600

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := State.addr s.sp - BitVec.ofNat 64 600

abbrev OUT (s : State) : Region := ⟨State.addr (s.gpr .r0), 32⟩
abbrev EXP (s : State) : Region := ⟨State.addr (s.gpr .r1), 64⟩
abbrev SEED (s : State) : Region := ⟨State.addr (s.gpr .r2), 32⟩
abbrev SCR (s : State) : Region := ⟨State.addr (s.gpr .r3), 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 600⟩
abbrev TB (s : State) : Region := ⟨State.addr (s.syms combSym), 8 * combWords.length⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 600 ≤ s.sp.toNat
  rd : s.rd = [SEED s, TB s]
  wr : s.wr = [OUT s, EXP s, SCR s]
  held : ∀ i < combWords.length,
    s.mem.readW (State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0
  fit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 32
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
  no : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  ne : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  ns : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  nc : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨hsp, -, hd, hheld, hfit, hdw, hdk, hal, ht, hw, oe, os, oc, es, ec, sc,
    ko, ke, ks, kc, no, ne, ns, nc⟩ := h
  refine ⟨hsp, ?_, hw, hheld, hfit, hal, hdw _ (by rw [hw]; simp [State.addr]),
    hdw _ (by rw [hw]; simp [State.addr]), hdw _ (by rw [hw]; simp [State.addr]), hdk, oe, os, oc, es, ec, sc, ko, ke, ks, kc, no, ne, ns, nc⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl

/-- The precondition, from its facts. -/
theorem spec_of {s : State} (h : Pre s) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  refine ⟨h.sp, by have := s.sp.isLt; omega, by rw [h.rd]; rfl, h.held, h.fit, fun r hr => ?_, h.tK, h.al,
    by rw [h.rd]; rfl, h.wr, h.oe, h.os, h.oc, h.es, h.ec, h.sc, h.ko, h.ke, h.ks, h.kc, h.no, h.ne, h.ns,
    h.nc⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.tO
  · exact h.tE
  · exact h.tC

/-! ## Addresses on the stack -/

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sub_sub' (x : BitVec 32) (a b : Nat) :
    x - BitVec.ofNat 32 a - BitVec.ofNat 32 b = x - BitVec.ofNat 32 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]

/-- `sp - k`, as an offset of `K s`. -/
theorem addrK {s : State} (h : Pre s) {k : Nat} (hk : k ≤ 600) :
    State.addr (s.sp - BitVec.ofNat 32 k) = K s + BitVec.ofNat 64 (600 - k) := by
  rw [addr_sub' (by have := h.sp; omega)]
  exact Offset.sub_ofNat_eq _ hk

theorem K_toNat {s : State} (h : Pre s) {d : Nat} (hd : d ≤ 600) :
    (K s + BitVec.ofNat 64 d).toNat = s.sp.toNat - 600 + d := by
  have := h.sp
  have := s.sp.isLt
  simp only [K, State.addr, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 600) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint (TB s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  h.tK.sub_right (stk_sub s hd)

end Pre

/-! ## Between the pushes and the pops -/

/-- The saved arguments. -/
abbrev AR (s : State) : Region := ⟨K s + BitVec.ofNat 64 584, 12⟩
/-- Where `lr` is saved. -/
abbrev LR (s : State) : Region := ⟨K s + BitVec.ofNat 64 596, 4⟩

/-- What holds between the pushes and the pops, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = AR s :: LR s :: s.wr
  sp : t.sp = s.sp - BitVec.ofNat 32 16
  cs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r
  lr : t.mem.readW (K s + BitVec.ofNat 64 596) 32 = s.gpr .lr
  fOut : t.mem.readW (K s + BitVec.ofNat 64 584) 32 = s.gpr .r0
  fExp : t.mem.readW (K s + BitVec.ofNat 64 588) 32 = s.gpr .r1
  fScr : t.mem.readW (K s + BitVec.ofNat 64 592) 32 = s.gpr .r3
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

theorem Ctx.sp_toNat {s t : State} (h : Pre s) (hc : Ctx s t) : t.sp.toNat = s.sp.toNat - 16 := by
  rw [hc.sp, sub_toNat' (by have := h.sp; omega)]

/-- `sp + d`, from between the pushes and the pops. -/
theorem Ctx.addr_sp {s t : State} (h : Pre s) (hc : Ctx s t) {d : Nat} (hd : d ≤ 16) :
    State.addr (t.sp + BitVec.ofNat 32 d) = K s + BitVec.ofNat 64 (584 + d) := by
  have := s.sp.isLt
  rw [addr_add (by rw [hc.sp_toNat h]; omega), hc.sp, addrK h (by decide), add_add]

/-- The `n` bytes below `sp`, from between the pushes and the pops. -/
theorem Ctx.below {s t : State} (h : Pre s) (hc : Ctx s t) {n : Nat} (hn : n ≤ 584) :
    belowA t.sp n = ⟨K s + BitVec.ofNat 64 (584 - n), n⟩ := by
  simp only [belowA]
  rw [hc.sp, sub_sub', addrK h (by omega), show 600 - (16 + n) = 584 - n by omega]

/-- A write of a register the ABI does not preserve. -/
theorem Ctx.setReg {s t : State} (hc : Ctx s t) {r : Reg} (hr : r ∉ preserved) (x : BitVec 32) :
    Ctx s (t.setReg r x) :=
  ⟨hc.rd, hc.wr, hc.sp, fun q hq hq' => by
      have hne : ¬q = r := fun e => hr (e ▸ hq)
      rw [RegUpd.gpr_setReg_of_ne (h := hne)]; exact hc.cs q hq hq',
    hc.lr, hc.fOut, hc.fExp, hc.fScr, hc.sym, hc.frame⟩

/-- The state the body starts in. -/
abbrev entered (s : State) : State := pushed [.r0, .r1, .r3] (pushed [.lr] s)

theorem entered_ctx {s : State} (h : Pre s) : Ctx s (entered s) := by
  have hsp := h.sp
  have hlt := s.sp.isLt
  have h4 : 4 * [Reg.lr].length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; omega
  have e4 : (pushed [.lr] s).sp = s.sp - BitVec.ofNat 32 4 := rfl
  have h12 : 4 * [Reg.r0, .r1, .r3].length ≤ (pushed [.lr] s).sp.toNat := by
    rw [e4, sub_toNat' (by omega)]; simp only [List.length_cons, List.length_nil]; omega
  have e16 : (entered s).sp = s.sp - BitVec.ofNat 32 16 := by
    show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 12 = _
    rw [sub_sub']
  have em : (entered s).mem =
      storeWords (pushed [.lr] s).mem (s.sp - BitVec.ofNat 32 16) [s.gpr .r0, s.gpr .r1, s.gpr .r3] := by
    show storeWords _ (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 12) _ = _
    rw [sub_sub']; rfl
  have em₁ : (pushed [.lr] s).mem = storeWords s.mem (s.sp - BitVec.ofNat 32 4) [s.gpr .lr] := rfl
  have t16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  -- The saved arguments.
  have slot : ∀ i (hi : i < 3), (entered s).mem.readW (K s + BitVec.ofNat 64 (584 + 4 * i)) 32 =
      [s.gpr .r0, s.gpr .r1, s.gpr .r3][i] := fun i hi => by
    have e := Argon2.Arm.storeWords_readW (pushed [.lr] s).mem (s.sp - BitVec.ofNat 32 16)
      [s.gpr .r0, s.gpr .r1, s.gpr .r3] (by simp only [List.length_cons, List.length_nil]; omega) hi
    rw [addr_add (by rw [t16]; omega), addrK h (by decide), add_add] at e
    rw [em]; exact e
  -- The saved `lr`, which the second push leaves alone.
  have hf₂ : Frame [⟨K s + BitVec.ofNat 64 584, 12⟩] (pushed [.lr] s).mem (entered s).mem := by
    have := Argon2.Arm.pushed_stk (rs := [.r0, .r1, .r3]) (s := pushed [.lr] s) h12
    simp only [Argon2.Arm.stkR, e4, List.length_cons, List.length_nil] at this
    rwa [← addr_sub' (by rw [sub_toNat' (by omega)]; omega), sub_sub', addrK h (by decide)] at this
  have hf₁ : Frame [⟨State.addr s.sp - BitVec.ofNat 64 4, 4⟩] s.mem (pushed [.lr] s).mem :=
    Argon2.Arm.pushed_stk (rs := [.lr]) (s := s) h4
  have hk : STK s ∈ [OUT s, EXP s, SCR s, STK s] := by simp
  refine ⟨rfl, ?_, e16, fun _ _ _ => rfl, ?_, slot 0 (by decide), slot 1 (by decide), slot 2 (by decide), rfl,
    (hf₁.sub fun r hr => ?_).trans (hf₂.sub fun r hr => ?_)⟩
  · show (⟨State.addr (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 12), 12⟩ : Region) ::
      ⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩ :: s.wr = _
    rw [sub_sub', addrK h (by decide), addrK h (by decide)]
  · rw [hf₂.readW (r := ⟨K s + BitVec.ofNat 64 596, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)) (by decide), em₁]
    have e := Argon2.Arm.storeWords_readW s.mem (s.sp - BitVec.ofNat 32 4) [s.gpr .lr]
      (by rw [sub_toNat' (by omega)]; simp only [List.length_cons, List.length_nil]; omega) (i := 0) (by simp)
    rw [Nat.mul_zero, BitVec.add_zero, addrK h (by decide)] at e
    exact e
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, hk, Offset.sub_below _ (by decide) (by decide)⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, hk, stk_sub s (by decide)⟩

/-! ## The digest's arguments -/

theorem exec_ldrSp {u : State} {t : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (u.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (u.rd ++ u.wr) a 4) :
    exec (.ldrSp t off) u = some (u.setReg t (u.mem.readW a 32)) := by
  subst ha; simp [exec, ho, State.load32, hin]

theorem Ctx.inAR {s t : State} (hc : Ctx s t) {d : Nat} (hd : d + 4 ≤ 12) :
    InRegions (t.rd ++ t.wr) (K s + BitVec.ofNat 64 (584 + d)) 4 := by
  rw [hc.wr]
  exact ⟨AR s, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- The digest's arguments: `data = seed`, `len = 32`, `out = expanded`. -/
theorem digestArgs_ok {s : State} (h : Pre s) :
    WP isa (.block digestArgs) (entered s) fun u => Ctx s u ∧ u.gpr .r0 = s.gpr .r2 ∧
      u.gpr .r1 = BitVec.ofNat 32 32 ∧ u.gpr .r2 = s.gpr .r1 := by
  have hc := entered_ctx h
  have hl := hc.inAR (d := 4) (by decide)
  have ha := hc.addr_sp h (d := 4) (by decide)
  have e2 : (entered s).gpr .r2 = s.gpr .r2 := rfl
  generalize entered s = t at hc hl ha e2
  refine WP.block_cons_iff.mpr ⟨t.setReg .r0 (t.gpr .r2), rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := t.setReg .r0 (t.gpr .r2)) (t := .r2) (by decide) ha hl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ⟨((hc.setReg (by decide) _).setReg (by decide) _).setReg
    (by decide) _, ?_, ?_, ?_⟩⟩
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r1 by decide)),
      RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r2 by decide)), RegUpd.gpr_setReg_self, e2]
  · rw [RegUpd.gpr_setReg_self]; rfl
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r2 = Reg.r1 by decide)), RegUpd.gpr_setReg_self]
    exact hc.fExp

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

/-- After a call from between the pushes and the pops that writes `wr`
(within `out`, `expanded` and `scratch`) and `n` bytes below `sp`, `Ctx`
holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {n : Nat}
    (hn : n ≤ 584) (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hf : Frame (wr ++ [belowA t.sp n]) t.mem t'.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → t'.gpr r = t.gpr r) (hsy : t'.syms = t.syms) : Ctx s t' := by
  rw [hc.below h hn] at hf
  have keep : ∀ e, 584 ≤ e → e + 4 ≤ 600 →
      t'.mem.readW (K s + BitVec.ofNat 64 e) 32 = t.mem.readW (K s + BitVec.ofNat 64 e) 32 := by
    intro e h₁ h₂
    refine hf.readW (r := ⟨K s + BitVec.ofNat 64 e, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rcases hsub r hr with rfl | rfl | rfl
      · exact h.kO (by omega)
      · exact h.kE (by omega)
      · exact h.kC (by omega)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 596 (by decide) (by decide)).trans hc.lr, (keep 584 (by decide) (by decide)).trans hc.fOut,
    (keep 588 (by decide) (by decide)).trans hc.fExp, (keep 592 (by decide) (by decide)).trans hc.fScr,
    hsy.trans hc.sym, hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, stk_sub s (by omega)⟩

/-! ## The digest -/

abbrev dgCode : Prog isa := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H'

abbrev dgK : Contract isa := Spec.Sha512.digestContract Arm.abi 64 Spec.Sha512.sha512 584

theorem dg_verified : Verified Arm.target dgCode dgK := Proof.MdStream.Arm.Digest.sha512_digest

theorem dg_stack : armStack dgCode = 584 := by decide +kernel

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .r0 = s.gpr .r2)
    (hx1 : t.gpr .r1 = BitVec.ofNat 32 32) (hx2 : t.gpr .r2 = s.gpr .r1) :
    dgK.pre (t.callEntry.withRegions [SEED s] [EXP s]) := by
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow]
  have hle : 584 ≤ t.sp.toNat := by rw [hc.sp_toNat h]; have := h.sp; omega
  have hb := hc.below h (n := 584) (le_refl _)
  simp only [belowA, addr_sub' hle] at hb
  rw [hx0, hx1, hx2, hb]
  exact ⟨hle, by have := t.sp.isLt; omega, rfl, rfl, h.es.symm, h.kS (by decide), h.kE (by decide), h.ns, h.ne⟩

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
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (hx0 : t.gpr .r0 = s.gpr .r2)
    (hx1 : t.gpr .r1 = BitVec.ofNat 32 32) (hx2 : t.gpr .r2 = s.gpr .r1) :
    WP isa (.call dn dgCode) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (State.addr (s.gpr .r1)) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) := by
  refine WP.of_syms (WP.callF dg_verified.1 (dg_pre h hc hx0 hx1 hx2) (dg_cov h hc).1 (dg_cov h hc).2
    (by rw [dg_stack, hc.sp_toNat h]; have := h.sp; omega)
    (fun t' hrd hwr hsp hf hcs hpost hsy => ⟨?_, ?_⟩))
  · rw [dg_stack] at hf
    exact Ctx.call h hc (le_refl _) (by simp) hrd hwr hsp hf hcs hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
    rw [hx0, hx1, hx2] at hpost
    have hS : Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r2)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 :=
      hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

/-- The public key's arguments, from the saved ones. -/
theorem pkArgs_ok {s t : State} (h : Pre s) (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .r0 = s.gpr .r0 ∧
      t'.gpr .r1 = s.gpr .r1 ∧ t'.gpr .r2 = s.gpr .r3 := by
  have a0 := hc.addr_sp h (d := 0) (by decide)
  have a4 := hc.addr_sp h (d := 4) (by decide)
  have a8 := hc.addr_sp h (d := 8) (by decide)
  have i0 := hc.inAR (d := 0) (by decide)
  have i4 := hc.inAR (d := 4) (by decide)
  have i8 := hc.inAR (d := 8) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := t) (t := .r0) (by decide) a0 i0, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := t.setReg .r0 _) (t := .r1) (by decide) a4 i4, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := (t.setReg .r0 _).setReg .r1 _) (t := .r2) (by decide) a8 i8,
    WP.block_nil_iff.mpr
    ⟨((hc.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _, rfl, ?_, ?_, ?_⟩⟩
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r2 by decide)),
      RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r1 by decide)), RegUpd.gpr_setReg_self]
    exact hc.fOut
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r1 = Reg.r2 by decide)), RegUpd.gpr_setReg_self]
    exact hc.fExp
  · rw [RegUpd.gpr_setReg_self]
    exact hc.fScr

abbrev pkK : Contract isa := Proof.Ed25519.Arm.PublicKey.pkSpecE

abbrev pkRd (s : State) : List Region := [EXP s, TB s]
abbrev pkWr (s : State) : List Region := [OUT s, SCR s]

theorem pk_stack : armStack PublicKey.codeExpanded ≤ 280 := by decide +kernel

theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .r0 = s.gpr .r0)
    (hx1 : t.gpr .r1 = s.gpr .r1) (hx2 : t.gpr .r2 = s.gpr .r3)
    (hE : Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)) :
    pkK.pre (t.callEntry.withRegions (pkRd s) (pkWr s)) := by
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  have hle : 280 ≤ t.sp.toNat := by rw [hc.sp_toNat h]; have := h.sp; omega
  have hb := hc.below h (n := 280) (by decide)
  simp only [belowA, addr_sub' hle] at hb
  rw [hx0, hx1, hx2, hb, hc.sym]
  have hT : ∀ r ∈ [OUT s, EXP s, SCR s, STK s], (TB s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tO
    · exact h.tE
    · exact h.tC
    · exact h.tK
  refine ⟨hle, by have := t.sp.isLt; omega, rfl, fun i hi => ?_, h.fit, h.tO, h.tC, h.kT (by decide), h.al,
    rfl, rfl, h.oe, h.oc, h.ec, h.kO (by decide), h.kE (by decide), h.kC (by decide), h.no, h.ne, h.nc,
    _, by simp [Spec.Ed25519.bytesAt], hE⟩
  · exact (hc.frame.readW (r := TB s) (a := State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * i)) (w := 64)
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
theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (hx0 : t.gpr .r0 = s.gpr .r0)
    (hx1 : t.gpr .r1 = s.gpr .r1) (hx2 : t.gpr .r2 = s.gpr .r3)
    (hE : Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)) :
    WP isa (.call pn PublicKey.codeExpanded) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (State.addr (s.gpr .r1)) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) ∧
      Spec.Ed25519.bytesAt t'.mem (State.addr (s.gpr .r0)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) := by
  have hd := pk_stack
  refine WP.of_syms (WP.callF Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified.1
    (pk_pre h hc hx0 hx1 hx2 hE) (pk_cov h hc).1 (pk_cov h hc).2
    (by rw [hc.sp_toNat h]; have := h.sp; omega)
    (fun t' hrd hwr hsp hf hcs hpost hsy =>
      ⟨Ctx.call h hc (by omega) (by simp) hrd hwr hsp hf hcs hsy, ?_, ?_⟩))
  · rw [← hE]
    rw [hc.below h (by omega)] at hf
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · exact (h.kE (by omega)).symm
  · sig_post [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts] at hpost
    rw [hx0, hx1] at hpost
    exact hpost _ (by simp [Spec.Ed25519.bytesAt]) hE

/-! ## The whole function -/

/-- The body, from the pushes. -/
theorem body_ok {s : State} (h : Pre s) {dn pn : String} :
    WP isa (.seq (.block digestArgs) (.seq (.call dn dgCode) (.seq (.block pkArgs) (.call pn PublicKey.codeExpanded))))
      (entered s) fun t => Ctx s t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) ∧
      Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) := by
  refine WP.seq (WP.mono (digestArgs_ok h) fun t ⟨hc, hx0, hx1, hx2⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok h hc hx0 hx1 hx2) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok h hc) fun t' ⟨hc', hm, hx0, hx1, hx2⟩ => ?_)
  exact pk_ok h hc' hx0 hx1 hx2 (by rw [hm]; exact hE)

theorem popped_gpr_self (r : Reg) (n : Nat) (s : State) :
    (popped r n s).gpr r = s.mem.readW (State.addr s.sp) 32 := by
  simp [popped, State.setReg]

theorem sub16_add12 (x : BitVec 32) : x - BitVec.ofNat 32 16 + BitVec.ofNat 32 12 = x - BitVec.ofNat 32 4 := by
  rw [show (16 : Nat) = 4 + 12 from rfl, ← sub_sub', BitVec.sub_add_cancel]

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn dgCode pn PublicKey.codeExpanded) s fun s' => abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  have hsp := h.sp
  refine WP.frame (rs := [.lr]) (r := .lr) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) ?_
  refine WP.frame (rs := [.r0, .r1, .r3]) (r := .r3) (by decide)
    (by show 12 ≤ (s.sp - BitVec.ofNat 32 4).toNat; rw [sub_toNat' (by omega)]; omega) (by decide)
    (WP.mono (body_ok h) fun u ⟨hu, hE, hO⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩)
  · by_cases hl : r = .lr
    · subst hl
      rw [popped_gpr_self, popped_mem, popped_sp, show 4 * [Reg.r0, .r1, .r3].length = 12 from rfl, hu.sp,
        sub16_add12, addrK h (by decide)]
      exact hu.lr
    · have h3 : r ≠ .r3 := by rintro rfl; revert hr; decide
      rw [popped_gpr hl, popped_gpr h3]; exact hu.cs r hr hl
  · show u.sp + BitVec.ofNat 32 12 + BitVec.ofNat 32 4 = s.sp
    simp only [hu.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.sub_add_cancel]
  · sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts]
    exact ⟨hE, hO⟩

/-! ## Constant time -/

structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  sy : s₁.syms combSym = s₂.syms combSym

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts] at h
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
  rw [c₁.sp, c₂.sp, hp.sp]

abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .r0 = s.gpr .r2 ∧ t.gpr .r1 = BitVec.ofNat 32 32 ∧ t.gpr .r2 = s.gpr .r1
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
    Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r1 = s.gpr .r1 ∧ t.gpr .r2 = s.gpr .r3

/-- The blocks' addresses are offsets of `sp`. -/
theorem digestArgs_sp : RelCT isa (fun a b => a.sp = b.sp) (.block digestArgs) fun a b => a.sp = b.sp :=
  Whole.step_sp_ct (fun _ _ _ => rfl) (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h])
    (Whole.step_sp_ct (fun _ _ _ => rfl) Whole.block_nil_ct))

theorem pkArgs_sp : RelCT isa (fun a b => a.sp = b.sp) (.block pkArgs) fun a b => a.sp = b.sp :=
  Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h])
    (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) Whole.block_nil_ct))

abbrev Entered (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem body_ct {dn pn : String} :
    RelCT isa Entered (.seq (.block digestArgs) (.seq (.call dn dgCode) (.seq (.block pkArgs)
      (.call pn PublicKey.codeExpanded)))) fun _ _ => True := by
  have b₁ : RelCT isa Entered (.block digestArgs) (Rel Φ₁) := by
    intro a b ta tb a' b' hp e₁ e₂
    obtain ⟨ht, -⟩ := digestArgs_sp _ _ _ _ _ _ (by
      obtain ⟨s₁, s₂, -, -, hp, rfl, rfl⟩ := hp
      simp only [entered, pushed_sp, hp.sp]) e₁ e₂
    obtain ⟨s₁, s₂, h₁, h₂, hp', rfl, rfl⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := digestArgs_ok h₁
    obtain ⟨_, u₂, x₂, y₂⟩ := digestArgs_ok h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2⟩
  have b₂ : RelCT isa (Rel Φ₁) (.call dn dgCode) (Rel Φ₂) := by
    refine rel_wp (Whole.callEx dg_verified.1 dg_verified.2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hx0, hx1, hx2⟩ => digest_ok h hc hx0 hx1 hx2
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨d₁, i₁, x₁⟩, ⟨d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, dg_pre h₁ c₁ d₁ i₁ x₁, dg_pre h₂ c₂ d₂ i₂ x₂, ?_, (dg_cov h₁ c₁).1, (dg_cov h₁ c₁).2,
      (dg_cov h₂ c₂).1, (dg_cov h₂ c₂).2⟩
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, hp.sp, hp.r2, hp.r1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have b₃ : RelCT isa (Rel Φ₂) (.block pkArgs) (Rel Φ₃) :=
    rel_wp (pkArgs_sp.mono (fun _ _ hr => rel_sp hr) fun _ _ _ => trivial) fun _ _ h hc hE =>
      WP.mono (pkArgs_ok h hc) fun _ ⟨hc', hm, a, b, d⟩ => ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel Φ₃) (.call pn PublicKey.codeExpanded) fun _ _ => True := by
    refine Whole.callEx Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified.1
      Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified.2.1 fun a b hr => ?_
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨e₁, d₁, i₁, x₁⟩, ⟨e₂, d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, pk_pre h₁ c₁ d₁ i₁ x₁ e₁, pk_pre h₂ c₂ d₂ i₂ x₂ e₂, ?_, (pk_cov h₁ c₁).1,
      (pk_cov h₁ c₁).2, (pk_cov h₂ c₂).1, (pk_cov h₂ c₂).2⟩
    sig_pub [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, c₁.sym, c₂.sym, hp.sp, hp.r0, hp.r1, hp.r3, hp.sy]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact b₁.seq (b₂.seq (b₃.seq b₄))

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn dgCode pn PublicKey.codeExpanded) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => (pub_of h.2.2).sp) ?_)
  refine RelCT.frame (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_) ?_
  · rw [Argon2.Arm.push_eq (by decide) pa, Argon2.Arm.push_eq (by decide) pb, pushed_sp, pushed_sp,
      (pub_of hp.2.2).sp]
  refine RelCT.mono body_ct ?_ fun _ _ _ => trivial
  rintro a b ⟨a₀, b₀, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, pa₀, pb₀⟩, pa, pb⟩
  rw [Argon2.Arm.push_eq (by decide) pa₀] at pa
  rw [Argon2.Arm.push_eq (by decide) pb₀] at pb
  exact ⟨s₁, s₂, pre_of h₁, pre_of h₂, pub_of hp, Argon2.Arm.push_eq (by decide) pa,
    Argon2.Arm.push_eq (by decide) pb⟩

/-! ## A witness, and the artifact's obligation -/

/-- A state satisfying the precondition: `out` at `0x1000`, `expanded` at `0x2000`, the seed at
`0x3000`, `scratch` at `0x4000`, the stack below `0x9000` and the comb's tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := Proof.Ed25519.Arm.PublicKey.satMemTE
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem sat_pre : Pre satState := by
  have hl := Proof.Ed25519.Arm.combWords_length
  refine ⟨by decide, by simp only [satState, SEED, TB, hl]; rfl, rfl,
    fun i hi => by
      have e : State.addr (satState.syms combSym) = 0x100000 := by decide
      rw [e]; exact Proof.Ed25519.Arm.PublicKey.satMemTE_held i (by rw [← hl]; exact hi), by simp only [satState, hl]; decide,
    by decide,
    by simp only [TB, OUT, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, EXP, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, SCR, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, STK, hl]; exact Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩

theorem verified {dn pn : String} :
    Verified Arm.target (keyPair dn dgCode pn PublicKey.codeExpanded) spec :=
  ⟨fun _ h => keyPair_ok h, keyPair_ct, ⟨_, spec_of sat_pre⟩⟩

end VG.Proof.Ed25519.Arm.KeyPair
