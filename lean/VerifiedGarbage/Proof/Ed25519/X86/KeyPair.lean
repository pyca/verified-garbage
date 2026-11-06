module

public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.X86.KeyPair
public import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Verified
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Impl.Ed25519.X86.KeyPair
meta import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Verified
meta import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# Ed25519 key-pair derivation on x86

`keyPair` calls the one-shot SHA-512 digest, which writes the seed's digest to
`expanded`, and then `vg_ed25519_public_key_expanded`, which derives the
public key from it, each with its arguments pushed in a frame of their own.
Its proof uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`esp - 628` on entry): each call's arguments are at
`K s + 616`, its return address at `K s + 612`, and the callee uses the 612
bytes below.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86.KeyPair

open VG VG.X86 VG.X86.Wp VG.Impl.Ed25519.X86 VG.Impl.Ed25519.X86.KeyPair

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (X86.abi.withConsts combConsts) 628

abbrev esp (s : State) : BitVec 32 := s.gpr .esp

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := (esp s).setWidth 64 - BitVec.ofNat 64 628

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 32⟩
abbrev EXP (s : State) : Region := ⟨(arg s 1).setWidth 64, 64⟩
abbrev SEED (s : State) : Region := ⟨(arg s 2).setWidth 64, 32⟩
abbrev SCR (s : State) : Region := ⟨(arg s 3).setWidth 64, 8192⟩
abbrev ARGS (s : State) : Region := ⟨argAddr s 0, 16⟩
abbrev RET (s : State) : Region := ⟨(esp s).setWidth 64, 4⟩
abbrev STK (s : State) : Region := ⟨K s, 628⟩
abbrev TB (s : State) : Region := ⟨(s.syms combSym).setWidth 64, 8 * combWords.length⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 628 ≤ (esp s).toNat
  top : (esp s).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s.rd = [SEED s, TB s]
  wr : s.wr = [OUT s, EXP s, SCR s, ARGS s]
  held : ∀ i < combWords.length,
    s.mem.readW ((s.syms combSym).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0
  fit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 32
  tw : ∀ r ∈ s.wr, (TB s).Disjoint r
  tR : (TB s).Disjoint (RET s)
  tK : (TB s).Disjoint (STK s)
  al : (s.syms combSym).toNat % 64 = 0
  oe : (OUT s).Disjoint (EXP s)
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  oa : (OUT s).Disjoint (ARGS s)
  es : (EXP s).Disjoint (SEED s)
  ec : (EXP s).Disjoint (SCR s)
  ea : (EXP s).Disjoint (ARGS s)
  sc : (SEED s).Disjoint (SCR s)
  sa : (SEED s).Disjoint (ARGS s)
  ca : (SCR s).Disjoint (ARGS s)
  ro : (RET s).Disjoint (OUT s)
  re : (RET s).Disjoint (EXP s)
  rs : (RET s).Disjoint (SEED s)
  rc : (RET s).Disjoint (SCR s)
  ra : (RET s).Disjoint (ARGS s)
  ko : (STK s).Disjoint (OUT s)
  ke : (STK s).Disjoint (EXP s)
  ks : (STK s).Disjoint (SEED s)
  kc : (STK s).Disjoint (SCR s)
  ka : (STK s).Disjoint (ARGS s)
  no : (arg s 0).toNat + 32 ≤ 2 ^ 32
  ne : (arg s 1).toNat + 64 ≤ 2 ^ 32
  ns : (arg s 2).toNat + 32 ≤ 2 ^ 32
  nc : (arg s 3).toNat + 8192 ≤ 2 ^ 32

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨hsp, htop, hd, hheld, hfit, hdw, hdr, hdk, hal, ht, hw, oe, os, oc, oa, es, ec, ea, sc, sa, ca,
    ro, re, rs, rc, ra, ko, ke, ks, kc, ka, no, ne, ns, nc⟩ := h
  refine ⟨hsp, htop, ?_, hw, hheld, hfit, hdw, hdr, hdk, hal, oe, os, oc, oa, es, ec, ea, sc, sa, ca,
    ro, re, rs, rc, ra, ko, ke, ks, kc, ka, no, ne, ns, nc⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl

theorem spec_of {s : State} (h : Pre s) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  exact ⟨h.sp, h.top, by rw [h.rd]; rfl, h.held, h.fit, h.tw, h.tR, h.tK, h.al, by rw [h.rd]; rfl, h.wr,
    h.oe, h.os, h.oc, h.oa, h.es, h.ec, h.ea, h.sc, h.sa, h.ca, h.ro, h.re, h.rs, h.rc, h.ra,
    h.ko, h.ke, h.ks, h.kc, h.ka, h.no, h.ne, h.ns, h.nc⟩

/-! ## Addresses on the stack, as offsets of `K s` -/

theorem K_toNat {s : State} (h : Pre s) : (K s).toNat + 628 = (esp s).toNat := by
  have := h.sp
  simp only [K, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := (esp s).isLt
  omega

/-- `n` bytes below `esp`, as an offset of `K s`. -/
theorem below_eq {s : State} (h : Pre s) {n : Nat} (hn : n ≤ 628) :
    below (esp s) n = ⟨K s + BitVec.ofNat 64 (628 - n), n⟩ := by
  have hk := K_toNat h
  have := (esp s).isLt
  show (⟨(esp s - BitVec.ofNat 32 n).setWidth 64, n⟩ : Region) = _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ret_eq (s : State) : (esp s).setWidth 64 = K s + BitVec.ofNat 64 628 := by
  simp only [K, BitVec.sub_add_cancel]

/-- Argument `j`'s address, as an offset of `K s`. -/
theorem argAddr_eq {s : State} (h : Pre s) {j : Nat} (hj : j < 4) :
    argAddr s j = K s + BitVec.ofNat 64 (632 + 4 * j) := by
  have hk := K_toNat h
  have := h.top
  simp only [esp] at hk this
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `esp - n`, widened, as an offset of `K s`. -/
theorem sub_eq {s : State} (h : Pre s) {n : Nat} (hn : n ≤ 628) :
    (s.gpr .esp - BitVec.ofNat 32 n).setWidth 64 = K s + BitVec.ofNat 64 (628 - n) := by
  have e := congrArg Region.base (below_eq h hn)
  exact e

theorem sub16 (x : BitVec 32) : x - 4 - 4 - 4 - 4 = x - BitVec.ofNat 32 16 := by bv_omega

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a - BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a - b) := by
  have : b < 2 ^ 64 := by omega
  have : a - b < 2 ^ 64 := by omega
  bv_omega

theorem off_sub' (p : Addr) : p + BitVec.ofNat 64 612 - BitVec.ofNat 64 612 = p + BitVec.ofNat 64 0 := by
  bv_omega

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 628) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 628) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 628) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 628) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 628) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kA (h : Pre s) {d n : Nat} (hd : d + n ≤ 628) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (ARGS s) :=
  h.ka.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 628) : Region.Disjoint (TB s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  h.tK.sub_right (stk_sub s hd)
theorem tO (h : Pre s) : (TB s).Disjoint (OUT s) := h.tw _ (by rw [h.wr]; simp)
theorem tE (h : Pre s) : (TB s).Disjoint (EXP s) := h.tw _ (by rw [h.wr]; simp)
theorem tC (h : Pre s) : (TB s).Disjoint (SCR s) := h.tw _ (by rw [h.wr]; simp)
theorem tA (h : Pre s) : (TB s).Disjoint (ARGS s) := h.tw _ (by rw [h.wr]; simp)

end Pre

/-! ## Between the calls -/

/-- What holds throughout, for the entry state `s`: the function has no frame of its own. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  cs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

theorem Ctx.esp {s t : State} (hc : Ctx s t) : esp t = esp s := hc.cs .esp (by decide)

theorem ctx_refl (s : State) : Ctx s s := ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem Ctx.upd {s t t' : State} (hc : Ctx s t) {d : Reg} {v : BitVec 32} (hu : Upd t t' d v)
    (hd : d ∉ calleeSaved) : Ctx s t' :=
  ⟨hu.rd.trans hc.rd, hu.wr.trans hc.wr,
    fun r hr => (hu.other r (fun e => hd (e ▸ hr))).trans (hc.cs r hr),
    hu.syms.trans hc.sym, hu.mem ▸ hc.frame⟩

/-- The function's own arguments are where they were. -/
theorem Ctx.argKeep {s t : State} (h : Pre s) (hc : Ctx s t) {j : Nat} (hj : j < 4) :
    t.mem.readW (argAddr s j) 32 = arg s j := by
  refine hc.frame.readW (r := ARGS s) ?_ (fun r hr => ?_) (by decide)
  · show (⟨argAddr s 0, 16⟩ : Region).Contains _ _
    rw [argAddr_eq h hj, argAddr_eq h (by decide : 0 < 4)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.oa.symm
    · exact h.ea.symm
    · exact h.ca.symm
    · exact h.ka.symm

theorem Ctx.argIn {s t : State} (h : Pre s) (hc : Ctx s t) {j : Nat} (hj : j < 4) :
    InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 + 4 * j)) 4 := by
  have e : addr (t.gpr .esp) (4 + 4 * j) = argAddr s j := by
    rw [show t.gpr .esp = s.gpr .esp from hc.esp]; rfl
  rw [e, hc.wr, h.wr, argAddr_eq h hj]
  refine ⟨ARGS s, by simp, ?_⟩
  show (⟨argAddr s 0, 16⟩ : Region).Contains _ _
  rw [argAddr_eq h (by decide : 0 < 4)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem Ctx.argRead {s t : State} (h : Pre s) (hc : Ctx s t) {j d : Nat} (hj : j < 4) (hd : d = 4 + 4 * j) :
    t.mem.readW (addr (t.gpr .esp) d) 32 = arg s j := by
  have e : addr (t.gpr .esp) d = argAddr s j := by
    rw [show t.gpr .esp = s.gpr .esp from hc.esp, hd]; rfl
  rw [e]; exact hc.argKeep h hj

theorem Ctx.argIn' {s t : State} (h : Pre s) (hc : Ctx s t) {j d : Nat} (hj : j < 4) (hd : d = 4 + 4 * j) :
    InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) d) 4 := hd ▸ hc.argIn h hj

/-- The digest's arguments. -/
theorem digestArgs_ok {s t : State} (h : Pre s) (hc : Ctx s t) :
    WP isa (.block digestArgs) t fun t' => Ctx s t' ∧ t'.gpr .eax = arg s 2 ∧
      t'.gpr .ecx = BitVec.ofNat 32 32 ∧ t'.gpr .edx = arg s 1 := by
  refine wp_ldm rfl (hc.argIn' h (j := 2) (by decide) rfl) fun t₁ u₁ => ?_
  refine wp_movi fun t₂ u₂ => ?_
  have c₁ := hc.upd u₁ (by decide)
  have c₂ := c₁.upd u₂ (by decide)
  refine wp_ldm rfl (c₂.argIn' h (j := 1) (by decide) rfl) fun t₃ u₃ =>
    WP.block_nil ⟨c₂.upd u₃ (by decide), ?_, ?_, ?_⟩
  · rw [u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.gpr]
    exact hc.argRead h (j := 2) (by decide) rfl
  · rw [u₃.other .ecx (by decide), u₂.gpr]; rfl
  · rw [u₃.gpr]
    exact c₂.argRead h (j := 1) (by decide) rfl

/-! ## Memory -/

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

/-! ## The digest -/

abbrev dgCode : Prog isa := Impl.MdStream.X86.Digest.digest Proof.Pbkdf2.Stream.X86.sha512H'

abbrev dgK : Contract isa := Spec.Sha512.digestContract X86.abi 64 Spec.Sha512.sha512 612

theorem dg_verified : Verified X86.target dgCode dgK := Proof.MdStream.X86.Digest.sha512_digest

theorem dg_nosp : NoSp dgCode := by
  refine NoSp.of_all ?_
  have hm := Proof.MdStream.X86.Digest.noEsp Proof.Pbkdf2.Stream.X86.sha512OK
    Proof.MdStream.X86.Digest.sha512Shape_noEsp
  simp only [dgCode, Impl.MdStream.X86.Digest.digest, Impl.StackScratch.X86.withStackScratchWiped,
    Impl.StackScratch.X86.withStackScratch, Code.allInstrs, hm, Bool.true_and]
  decide

theorem dg_stack : stackUse dgCode ≤ 612 := by
  have hm := Proof.MdStream.X86.Digest.digestMain_stack Proof.Pbkdf2.Stream.X86.sha512OK
  simp only [dgCode, Impl.MdStream.X86.Digest.digest, Impl.StackScratch.X86.withStackScratchWiped,
    Impl.StackScratch.X86.withStackScratch, stackUse]
  have hf : frameBytes (Instr.alloc (Impl.MdStream.X86.Digest.dframe Proof.Pbkdf2.Stream.X86.sha512H')) = 564 :=
    rfl
  rw [hf]
  generalize stackUse (Impl.MdStream.X86.Digest.digestMain Proof.Pbkdf2.Stream.X86.sha512H') = x at hm ⊢
  simp only [Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right hm 564

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (ha : t.gpr .eax = arg s 2)
    (hc' : t.gpr .ecx = BitVec.ofNat 32 32) (hd : t.gpr .edx = arg s 1) :
    dgK.pre ((pushed argRegs t).callEntry.withRegions [SEED s, below (t.gpr .esp) 12] [EXP s]) := by
  have hfit : 4 * argRegs.length + 4 ≤ (t.gpr .esp).toNat := by
    show 16 ≤ _; rw [show t.gpr .esp = s.gpr .esp from hc.esp]; have := h.sp; simp only [esp] at this; omega
  have a0 : arg (pushed argRegs t).callEntry 0 = arg s 2 :=
    (callEntry_arg hfit (by decide) (by decide)).trans ha
  have a1 : arg (pushed argRegs t).callEntry 1 = BitVec.ofNat 32 32 :=
    (callEntry_arg hfit (by decide) (by decide)).trans hc'
  have a2 : arg (pushed argRegs t).callEntry 2 = arg s 1 :=
    (callEntry_arg hfit (by decide) (by decide)).trans hd
  have b0 : argAddr (pushed argRegs t).callEntry 0 = (below (t.gpr .esp) 12).base :=
    callEntry_argAddr0 argRegs t
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, stackBelow]
  have e := hc.esp
  simp only [esp] at e
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, b0, sub16, e,
    show (BitVec.ofNat 32 32).toNat = 32 from rfl,
    sub_eq h (show 16 ≤ 628 by decide), sub_eq h (show 12 ≤ 628 by decide), Nat.reduceSub]
  rw [off_sub' (K s), below_eq h (by decide)]
  have hk := K_toNat h
  have ht := h.top
  simp only [esp] at hk ht
  refine ⟨?_, ?_, rfl, trivial, h.es.symm, (h.kE (by decide)).symm, h.kS (by decide), h.kE (by decide),
    Offset.disjoint _ (by omega) (by omega) (by omega), h.kS (by decide), h.kE (by decide),
    Offset.disjoint _ (by omega) (by omega) (by omega), h.ns, h.ne⟩
  · rw [sub_toNat (by omega)]; omega
  · rw [sub_toNat (by omega)]; omega

/-- `STK s`, as the stack below `esp`. -/
theorem stk_below {s : State} (h : Pre s) : STK s = below (s.gpr .esp) 628 := by
  rw [show s.gpr .esp = esp s from rfl, below_eq h (le_refl _)]
  simp

/-- What a call from the entry `esp` may change below it, `n ≤ 628` bytes, is in the stack used. -/
theorem below_stk {s t : State} (h : Pre s) (hc : Ctx s t) {n : Nat} (hn : n ≤ 628) :
    Region.Sub (below (t.gpr .esp) n) (STK s) := by
  rw [show t.gpr .esp = s.gpr .esp from hc.esp, stk_below h]
  exact below_sub hn (by have := h.sp; simpa only [esp] using this)

/-- After a call that writes `wr` (within `out`, `expanded` and `scratch`) and the
`n ≤ 628` bytes below `esp`, `Ctx` holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {n : Nat} (hn : n ≤ 628)
    (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s ∨ Region.Sub r (STK s))
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame (wr ++ [below (t.gpr .esp) n]) t.mem t'.mem) (hsy : t'.syms = t.syms) : Ctx s t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r hr => (hcs r hr).trans (hc.cs r hr), hsy.trans hc.sym,
    hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl | hk
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, hk⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, below_stk h hc hn⟩

theorem dg_cp {s t : State} (h : Pre s) (hc : Ctx s t) (ha : t.gpr .eax = arg s 2)
    (hc' : t.gpr .ecx = BitVec.ofNat 32 32) (hd : t.gpr .edx = arg s 1) :
    CallPre dgK argRegs [SEED s, below (t.gpr .esp) 12] [EXP s] t := by
  refine ⟨dg_pre h hc ha hc' hd, Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [argRegs]
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp

/-- The digest's call, its arguments pushed: the seed's digest at `expanded`. -/
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (ha : t.gpr .eax = arg s 2)
    (hc' : t.gpr .ecx = BitVec.ofNat 32 32) (hd : t.gpr .edx = arg s 1) :
    WP isa (.frame (.push argRegs) (.call dn dgCode) (.pop .eax 3)) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem ((arg s 1).setWidth 64) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32) := by
  have e := hc.esp
  simp only [esp] at e
  have hsp := h.sp
  simp only [esp] at hsp
  have hu := dg_stack
  have hfit : 4 * argRegs.length + 4 ≤ (t.gpr .esp).toNat := by show 16 ≤ _; rw [e]; omega
  have cp := dg_cp h hc ha hc' hd
  have hn : 4 * argRegs.length + stackUse dgCode + 4 ≤ 628 := by
    rw [show 4 * argRegs.length = 12 from rfl]
    generalize stackUse dgCode = u at hu ⊢
    omega
  refine WP.of_syms (WP.callWith dg_verified.1 dg_nosp (by decide) (by decide)
    (hn.trans (by rw [e]; exact hsp)) cp fun t' hrd hwr hcs hf ⟨s₂, hm₂, hpost⟩ hsy => ⟨?_, ?_⟩)
  · exact Ctx.call h hc hn (by simp) hrd hwr hcs hf hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes] at hpost
    change Spec.Sha512.bytesAt _ _ 64 =
      Spec.Sha512.sha512 (Spec.Sha512.bytesAt (pushed argRegs t).callEntry.mem _ _) at hpost
    have a0 : arg (pushed argRegs t).callEntry 0 = arg s 2 :=
      (callEntry_arg hfit (by decide) (by decide)).trans ha
    have a1 : arg (pushed argRegs t).callEntry 1 = BitVec.ofNat 32 32 :=
      (callEntry_arg hfit (by decide) (by decide)).trans hc'
    have a2 : arg (pushed argRegs t).callEntry 2 = arg s 1 :=
      (callEntry_arg hfit (by decide) (by decide)).trans hd
    simp only [arg_withRegions, a0, a1, a2, hm₂, show (BitVec.ofNat 32 32).toNat = 32 from rfl] at hpost
    have hce := callEntry_frame hfit (by decide : Reg.esp ∉ argRegs)
    have hS : Spec.Ed25519.bytesAt (pushed argRegs t).callEntry.mem ((arg s 2).setWidth 64) 32 =
        Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32 := by
      rw [bytesAt_frame hce (fun r hr => ?_) (by decide)]
      · exact hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
      · rw [List.mem_singleton.mp hr]
        exact h.ks.symm.sub_right (below_stk h hc (by decide))
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

theorem pkArgs_ok {s t : State} (h : Pre s) (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .eax = arg s 0 ∧
      t'.gpr .ecx = arg s 1 ∧ t'.gpr .edx = arg s 3 := by
  refine wp_ldm rfl (hc.argIn' h (j := 0) (by decide) rfl) fun t₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide)
  refine wp_ldm rfl (c₁.argIn' h (j := 1) (by decide) rfl) fun t₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide)
  refine wp_ldm rfl (c₂.argIn' h (j := 3) (by decide) rfl) fun t₃ u₃ =>
    WP.block_nil ⟨c₂.upd u₃ (by decide), by rw [u₃.mem, u₂.mem, u₁.mem], ?_, ?_, ?_⟩
  · rw [u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.gpr]
    exact hc.argRead h (j := 0) (by decide) rfl
  · rw [u₃.other .ecx (by decide), u₂.gpr]
    exact c₁.argRead h (j := 1) (by decide) rfl
  · rw [u₃.gpr]
    exact c₂.argRead h (j := 3) (by decide) rfl

abbrev pkK : Contract isa := Spec.Ed25519.publicKeyExpandedContract (X86.abi.withConsts combConsts) 280

theorem pk_nosp : NoSp PublicKey.publicKeyExpanded := by
  intro i hi
  simp only [PublicKey.publicKeyExpanded, instrs, List.cons_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | hi | rfl
  · decide
  · exact PublicKey.bodyFrom_nosp PublicKey.copy_nosp i hi
  · decide

theorem pk_stack : stackUse PublicKey.publicKeyExpanded ≤ 280 := by
  simp only [PublicKey.publicKeyExpanded, PublicKey.bodyFrom, PublicKey.callWith, PublicKey.copyExpanded,
    stackUse, frameBytes, PublicKey.base_stack, List.length_replicate]
  decide

abbrev pkRd (s : State) : List Region := [EXP s, TB s]
abbrev pkWr (s t : State) : List Region := [OUT s, SCR s, below (t.gpr .esp) 12]

theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (ha : t.gpr .eax = arg s 0)
    (hc' : t.gpr .ecx = arg s 1) (hd : t.gpr .edx = arg s 3)
    (hE : Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)) :
    pkK.pre ((pushed argRegs t).callEntry.withRegions (pkRd s) (pkWr s t)) := by
  have e := hc.esp
  simp only [esp] at e
  have hsp := h.sp
  simp only [esp] at hsp
  have hfit : 4 * argRegs.length + 4 ≤ (t.gpr .esp).toNat := by show 16 ≤ _; rw [e]; omega
  have hce := callEntry_frame hfit (by decide : Reg.esp ∉ argRegs)
  have hheld : ∀ i < combWords.length, (pushed argRegs t).callEntry.mem.readW
      ((s.syms combSym).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
    intro i hi
    have hn := h.fit
    rw [hce.readW (r := TB s) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide),
      hc.frame.readW (r := TB s) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)]
    · exact h.held i hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.tO
      · exact h.tE
      · exact h.tC
      · exact h.tK
    · rw [List.mem_singleton.mp hr]; exact h.tK.sub_right (below_stk h hc (by decide))
  have hk' : Spec.Ed25519.bytesAt (pushed argRegs t).callEntry.mem ((arg s 1).setWidth 64) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32) := by
    refine (bytesAt_frame hce (fun r hr => ?_) (by decide)).trans hE
    rw [List.mem_singleton.mp hr]; exact h.ke.symm.sub_right (below_stk h hc (by decide))
  have a0 : arg (pushed argRegs t).callEntry 0 = arg s 0 :=
    (callEntry_arg hfit (by decide) (by decide)).trans ha
  have a1 : arg (pushed argRegs t).callEntry 1 = arg s 1 :=
    (callEntry_arg hfit (by decide) (by decide)).trans hc'
  have a2 : arg (pushed argRegs t).callEntry 2 = arg s 3 :=
    (callEntry_arg hfit (by decide) (by decide)).trans hd
  have b0 : argAddr (pushed argRegs t).callEntry 0 = K s + BitVec.ofNat 64 616 := by
    rw [callEntry_argAddr0 argRegs t, e]; exact sub_eq h (n := 12) (by decide)
  have hesp : (pushed argRegs t).callEntry.gpr .esp = s.gpr .esp - 16#32 := by
    rw [callEntry_esp', e]; rfl
  generalize hX : (pushed argRegs t).callEntry.withRegions (pkRd s) (pkWr s t) = X
  have xm : X.mem = (pushed argRegs t).callEntry.mem := by rw [← hX]; rfl
  have xsp : X.gpr .esp = s.gpr .esp - 16#32 := by rw [← hX]; exact hesp
  have x0 : arg X 0 = arg s 0 := by rw [← hX, arg_withRegions]; exact a0
  have x1 : arg X 1 = arg s 1 := by rw [← hX, arg_withRegions]; exact a1
  have x2 : arg X 2 = arg s 3 := by rw [← hX, arg_withRegions]; exact a2
  have xb : argAddr X 0 = K s + BitVec.ofNat 64 616 := by rw [← hX, argAddr_withRegions]; exact b0
  have xsy : X.syms = s.syms := by rw [← hX]; exact hc.sym
  have xrd : X.rd = pkRd s := by rw [← hX]; rfl
  have xwr : X.wr = pkWr s t := by rw [← hX]; rfl
  have xheld : ∀ i < combWords.length,
      X.mem.readW ((s.syms combSym).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
    rw [xm]; exact hheld
  have xk : Spec.Ed25519.bytesAt X.mem ((arg s 1).setWidth 64) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32) := by rw [xm]; exact hk'
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  simp only [x0, x1, x2, xb, xsy, xrd, xwr, xsp, sub_eq h (show 16 ≤ 628 by decide), Nat.reduceSub]
  rw [off_sub _ (b := 280) (by decide) (by decide)]
  have hk := K_toNat h
  have ht := h.top
  simp only [esp] at hk ht
  have k12 : below (t.gpr .esp) 12 = ⟨K s + BitVec.ofNat 64 616, 12⟩ := by rw [e]; exact below_eq h (by decide)
  have hd : ∀ {a b : Nat}, a + 4 ≤ b → b + 12 ≤ 628 →
      Region.Disjoint ⟨K s + BitVec.ofNat 64 a, 4⟩ ⟨K s + BitVec.ofNat 64 b, 12⟩ :=
    fun h₁ h₂ => Offset.disjoint _ (by omega) (by omega) (by omega)
  have hd' : Region.Disjoint ⟨K s + BitVec.ofNat 64 (612 - 280), 280⟩ ⟨K s + BitVec.ofNat 64 616, 12⟩ :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; omega, rfl, xheld, h.fit,
    fun r hr => ?_, h.kT (by decide), h.kT (by decide), h.al, rfl, by simp only [pkWr, k12], h.oe, h.oc,
    (h.kO (by decide)).symm, h.ec, (h.kE (by decide)).symm, (h.kC (by decide)).symm,
    h.kO (by decide), h.kE (by decide), h.kC (by decide), hd (by decide) (by decide),
    h.kO (by decide), h.kE (by decide), h.kC (by decide), hd',
    h.no, h.ne, h.nc, ⟨_, by simp [Spec.Ed25519.bytesAt], xk⟩⟩
  simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.tO
  · exact h.tC
  · rw [k12]; exact h.kT (by decide)

theorem pk_cp {s t : State} (h : Pre s) (hc : Ctx s t) (ha : t.gpr .eax = arg s 0)
    (hc' : t.gpr .ecx = arg s 1) (hd : t.gpr .edx = arg s 3)
    (hE : Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)) :
    CallPre pkK argRegs (pkRd s) (pkWr s t) t := by
  refine ⟨pk_pre h hc ha hc' hd hE, Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [pkRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [argRegs]
  · rw [hc.wr, h.wr]
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [argRegs]

theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (ha : t.gpr .eax = arg s 0)
    (hc' : t.gpr .ecx = arg s 1) (hd : t.gpr .edx = arg s 3)
    (hE : Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)) :
    WP isa (.frame (.push argRegs) (.call pn PublicKey.publicKeyExpanded) (.pop .eax 3)) t fun t' =>
      Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem ((arg s 1).setWidth 64) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32) ∧
      Spec.Ed25519.bytesAt t'.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32) := by
  have e := hc.esp
  simp only [esp] at e
  have hsp := h.sp
  simp only [esp] at hsp
  have hu := pk_stack
  have hfit : 4 * argRegs.length + 4 ≤ (t.gpr .esp).toNat := by show 16 ≤ _; rw [e]; omega
  have k12 : below (t.gpr .esp) 12 = ⟨K s + BitVec.ofNat 64 616, 12⟩ := by rw [e]; exact below_eq h (by decide)
  have cp := pk_cp h hc ha hc' hd hE
  have hn : 4 * argRegs.length + stackUse PublicKey.publicKeyExpanded + 4 ≤ 628 := by
    rw [show 4 * argRegs.length = 12 from rfl]
    generalize stackUse PublicKey.publicKeyExpanded = u at hu ⊢
    omega
  have hfit' := hfit
  refine WP.of_syms (WP.callWith PublicKey.publicKeyExpanded_verified.1 pk_nosp (by decide) (by decide)
    (hn.trans (by rw [e]; exact hsp)) cp fun t' hrd hwr hcs hf ⟨s₂, hm₂, hpost⟩ hsy => ⟨?_, ?_, ?_⟩)
  · refine Ctx.call h hc hn (fun r hr => ?_) hrd hwr hcs hf hsy
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr (by rw [k12]; exact stk_sub s (by decide))))
  · rw [← hE]
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · rw [k12]; exact (h.kE (by decide)).symm
    · exact h.ke.symm.sub_right (below_stk h hc hn)
  · have a0 : arg (pushed argRegs t).callEntry 0 = arg s 0 :=
      (callEntry_arg hfit' (by decide) (by decide)).trans ha
    have a1 : arg (pushed argRegs t).callEntry 1 = arg s 1 :=
      (callEntry_arg hfit' (by decide) (by decide)).trans hc'
    have hce := callEntry_frame hfit' (by decide : Reg.esp ∉ argRegs)
    have hk' : Spec.Ed25519.bytesAt (pushed argRegs t).callEntry.mem ((arg s 1).setWidth 64) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32) := by
      refine (bytesAt_frame hce (fun r hr => ?_) (by decide)).trans hE
      rw [List.mem_singleton.mp hr]; exact h.ke.symm.sub_right (below_stk h hc (by decide))
    generalize hX : (pushed argRegs t).callEntry.withRegions (pkRd s) (pkWr s t) = X at hpost
    have xm : X.mem = (pushed argRegs t).callEntry.mem := by rw [← hX]; rfl
    have x0 : arg X 0 = arg s 0 := by rw [← hX, arg_withRegions]; exact a0
    have x1 : arg X 1 = arg s 1 := by rw [← hX, arg_withRegions]; exact a1
    sig_post [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts] at hpost
    simp only [x0, x1, xm, hm₂] at hpost
    exact hpost _ (by simp [Spec.Ed25519.bytesAt]) hk'

/-! ## The whole function -/

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn dgCode pn PublicKey.publicKeyExpanded) s fun s' =>
      abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  refine WP.seq (WP.mono (digestArgs_ok h (ctx_refl s)) fun t ⟨hc, ha, hc', hd⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok h hc ha hc' hd) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok h hc) fun t' ⟨hc', hm, ha, hc'', hd⟩ => ?_)
  refine WP.mono (pk_ok h hc' ha hc'' hd (by rw [hm]; exact hE)) fun u ⟨hu, hE', hO⟩ => ⟨⟨hu.cs, ?_⟩, ?_⟩
  · refine hu.frame.readW (r := RET s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.ro
    · exact h.re
    · exact h.rc
    · show Region.Disjoint ⟨(esp s).setWidth 64, 4⟩ ⟨K s, 628⟩
      rw [ret_eq s]; exact Offset.disjoint_base _ (by decide) (by decide)
  · sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq, Abi.withConsts]
    exact ⟨hE', hO⟩

/-! ## Constant time -/

/-- The taint of the argument blocks: only `esp` is public. -/
def τ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false }

theorem τ₀_wf (u : State) : VG.X86.Taint.Wf τ₀ u :=
  VG.X86.Taint.Wf.entry rfl rfl
    { lens := fun h => absurd rfl h
      bases := fun _ h => by simp [τ₀] at h
      wbases := fun _ h => by simp [τ₀] at h
      args := fun h => by simp [τ₀] at h
      argBases := fun _ h => by simp [τ₀] at h }

theorem τ₀_agree {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τ₀ s₁ s₂ where
  rf := ⟨fun r hr => by
    have := RegSet.mem_ofList.mp hr
    simp only [List.mem_singleton] at this
    subst this; exact h, fun h => by simp [τ₀] at h⟩
  wr h := absurd rfl h
  wf₁ := τ₀_wf _
  wf₂ := τ₀_wf _
  ok _ _ h := by simp [τ₀, VG.Slots.has_empty] at h
  slots _ _ h := by simp [τ₀, VG.Slots.has_empty] at h
  sp h := by simp [τ₀] at h
  argMem _ _ h := by simp [τ₀] at h

structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.gpr .esp = s₂.gpr .esp
  sy : s₁.syms combSym = s₂.syms combSym
  a0 : arg s₁ 0 = arg s₂ 0
  a1 : arg s₁ 1 = arg s₂ 1
  a2 : arg s₁ 2 = arg s₂ 2
  a3 : arg s₁ 3 = arg s₂ 3

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq, Abi.withConsts] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3⟩ := h
  exact ⟨hsp, hsy, h0, h1, h2, h3⟩

theorem Pub.refl (s : State) : Pub s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two runs between the calls, from entry states that agree with `S` on what is public. -/
def Rel (S : State) (Φ : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub S s₁ ∧ Pub S s₂ ∧ Ctx s₁ a ∧ Ctx s₂ b ∧ Φ s₁ a ∧ Φ s₂ b

theorem rel_wp {S : State} {c : Prog isa} {Φ Ψ : State → State → Prop}
    (hct : RelCT isa (Rel S Φ) c fun _ _ => True)
    (hw : ∀ s t, Pre s → Ctx s t → Φ s t → WP isa c t fun t' => Ctx s t' ∧ Ψ s t') :
    RelCT isa (Rel S Φ) c (Rel S Ψ) := by
  intro a b ta tb a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, h₁, h₂, p₁, p₂, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ a h₁ c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ b h₂ c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, s₁, s₂, h₁, h₂, p₁, p₂, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem Rel.esp₁ {S : State} {Φ : State → State → Prop} {a b : State} (h : Rel S Φ a b) :
    a.gpr .esp = S.gpr .esp := by
  obtain ⟨_, _, _, _, p₁, _, c₁, _⟩ := h
  exact c₁.esp.trans p₁.sp.symm

theorem Rel.esp₂ {S : State} {Φ : State → State → Prop} {a b : State} (h : Rel S Φ a b) :
    b.gpr .esp = S.gpr .esp := by
  obtain ⟨_, _, _, _, _, p₂, _, c₂, _⟩ := h
  exact c₂.esp.trans p₂.sp.symm

theorem rel_block {S : State} {is : List Instr} {Φ Ψ : State → State → Prop}
    {hc : VG.Taint.Hint VG.X86.Taint.T} (ht : (taint.check τ₀ (.block is) hc).isSome = true)
    (hw : ∀ s t, Pre s → Ctx s t → Φ s t → WP isa (.block is) t fun t' => Ctx s t' ∧ Ψ s t') :
    RelCT isa (Rel S Φ) (.block is) (Rel S Ψ) :=
  rel_wp (RelCT.taint (A := taint) τ₀ (fun _ _ h => τ₀_agree (h.esp₁.trans h.esp₂.symm)) ht) hw

abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .eax = arg s 2 ∧ t.gpr .ecx = BitVec.ofNat 32 32 ∧ t.gpr .edx = arg s 1
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 64 =
    Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .eax = arg s 0 ∧ t.gpr .ecx = arg s 1 ∧ t.gpr .edx = arg s 3

theorem regions_eq {S s : State} (p : Pub S s) :
    SEED s = SEED S ∧ EXP s = EXP S ∧ OUT s = OUT S ∧ SCR s = SCR S ∧ TB s = TB S := by
  simp only [SEED, EXP, OUT, SCR, TB, p.a0, p.a1, p.a2, p.a3, p.sy]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem body_ct (S : State) {dn pn : String} :
    RelCT isa (Rel S fun _ _ => True) (keyPair dn dgCode pn PublicKey.publicKeyExpanded) fun _ _ => True := by
  have b₁ : RelCT isa (Rel S fun _ _ => True) (.block digestArgs) (Rel S Φ₁) :=
    rel_block (by taint_decide) fun _ _ h hc _ => WP.mono (digestArgs_ok h hc) fun _ ⟨hc', a, b, d⟩ =>
      ⟨hc', a, b, d⟩
  have b₂ : RelCT isa (Rel S Φ₁) (.frame (.push argRegs) (.call dn dgCode) (.pop .eax 3)) (Rel S Φ₂) := by
    refine rel_wp (RelCT.callWith dg_verified.1 dg_verified.2.1 [SEED S, below (S.gpr .esp) 12] [EXP S]
      fun a b hr => ?_) fun s _ h hc ⟨ha, hc', hd⟩ => digest_ok h hc ha hc' hd
    have ea := hr.esp₁
    have eb := hr.esp₂
    obtain ⟨s₁, s₂, h₁, h₂, p₁, p₂, c₁, c₂, ⟨a₁, b₁, d₁⟩, ⟨a₂, b₂, d₂⟩⟩ := hr
    obtain ⟨r₁, r₁', -⟩ := regions_eq p₁
    obtain ⟨r₂, r₂', -⟩ := regions_eq p₂
    have k₁ := dg_cp h₁ c₁ a₁ b₁ d₁
    have k₂ := dg_cp h₂ c₂ a₂ b₂ d₂
    rw [r₁, r₁', ea] at k₁
    rw [r₂, r₂', eb] at k₂
    refine ⟨k₁, k₂, ea.trans eb.symm, ?_⟩
    have f₁ : 4 * argRegs.length + 4 ≤ (a.gpr .esp).toNat := by
      rw [show a.gpr .esp = s₁.gpr .esp from c₁.esp]; have := h₁.sp; simp only [esp] at this
      show 16 ≤ _; omega
    have f₂ : 4 * argRegs.length + 4 ≤ (b.gpr .esp).toNat := by
      rw [show b.gpr .esp = s₂.gpr .esp from c₂.esp]; have := h₂.sp; simp only [esp] at this
      show 16 ≤ _; omega
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, ea, eb,
      callEntry_arg f₁ (by decide : Reg.esp ∉ argRegs) (show 0 < 3 by decide),
      callEntry_arg f₂ (by decide : Reg.esp ∉ argRegs) (show 0 < 3 by decide),
      callEntry_arg f₁ (by decide : Reg.esp ∉ argRegs) (show 1 < 3 by decide),
      callEntry_arg f₂ (by decide : Reg.esp ∉ argRegs) (show 1 < 3 by decide),
      callEntry_arg f₁ (by decide : Reg.esp ∉ argRegs) (show 2 < 3 by decide),
      callEntry_arg f₂ (by decide : Reg.esp ∉ argRegs) (show 2 < 3 by decide)]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · show a.gpr .eax = b.gpr .eax; rw [a₁, a₂, ← p₁.a2, ← p₂.a2]
    · show a.gpr .ecx = b.gpr .ecx; rw [b₁, b₂]
    · show a.gpr .edx = b.gpr .edx; rw [d₁, d₂, ← p₁.a1, ← p₂.a1]
  have b₃ : RelCT isa (Rel S Φ₂) (.block pkArgs) (Rel S Φ₃) :=
    rel_block (by taint_decide) fun _ _ h hc hE => WP.mono (pkArgs_ok h hc) fun _ ⟨hc', hm, a, b, d⟩ =>
      ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel S Φ₃) (.frame (.push argRegs) (.call pn PublicKey.publicKeyExpanded) (.pop .eax 3))
      fun _ _ => True := by
    refine RelCT.callWith PublicKey.publicKeyExpanded_verified.1 PublicKey.publicKeyExpanded_verified.2.1
      (pkRd S) (pkWr S S) fun a b hr => ?_
    have ea := hr.esp₁
    have eb := hr.esp₂
    obtain ⟨s₁, s₂, h₁, h₂, p₁, p₂, c₁, c₂, ⟨e₁, a₁, b₁, d₁⟩, ⟨e₂, a₂, b₂, d₂⟩⟩ := hr
    obtain ⟨-, r₁e, r₁o, r₁c, r₁t⟩ := regions_eq p₁
    obtain ⟨-, r₂e, r₂o, r₂c, r₂t⟩ := regions_eq p₂
    have k₁ := pk_cp h₁ c₁ a₁ b₁ d₁ e₁
    have k₂ := pk_cp h₂ c₂ a₂ b₂ d₂ e₂
    simp only [pkRd, pkWr, r₁e, r₁o, r₁c, r₁t, ea] at k₁
    simp only [pkRd, pkWr, r₂e, r₂o, r₂c, r₂t, eb] at k₂
    refine ⟨k₁, k₂, ea.trans eb.symm, ?_⟩
    have f₁ : 4 * argRegs.length + 4 ≤ (a.gpr .esp).toNat := by
      rw [show a.gpr .esp = s₁.gpr .esp from c₁.esp]; have := h₁.sp; simp only [esp] at this
      show 16 ≤ _; omega
    have f₂ : 4 * argRegs.length + 4 ≤ (b.gpr .esp).toNat := by
      rw [show b.gpr .esp = s₂.gpr .esp from c₂.esp]; have := h₂.sp; simp only [esp] at this
      show 16 ≤ _; omega
    sig_pub [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, combConsts_eq,
      Abi.withConsts]
    simp only [arg_withRegions, ea, eb,
      callEntry_arg f₁ (by decide : Reg.esp ∉ argRegs) (show 0 < 3 by decide),
      callEntry_arg f₂ (by decide : Reg.esp ∉ argRegs) (show 0 < 3 by decide),
      callEntry_arg f₁ (by decide : Reg.esp ∉ argRegs) (show 1 < 3 by decide),
      callEntry_arg f₂ (by decide : Reg.esp ∉ argRegs) (show 1 < 3 by decide),
      callEntry_arg f₁ (by decide : Reg.esp ∉ argRegs) (show 2 < 3 by decide),
      callEntry_arg f₂ (by decide : Reg.esp ∉ argRegs) (show 2 < 3 by decide)]
    refine ⟨trivial, by rw [c₁.sym, c₂.sym, ← p₁.sy, ← p₂.sy], ?_, ?_, ?_⟩
    · show a.gpr .eax = b.gpr .eax; rw [a₁, a₂, ← p₁.a0, ← p₂.a0]
    · show a.gpr .ecx = b.gpr .ecx; rw [b₁, b₂, ← p₁.a1, ← p₂.a1]
    · show a.gpr .edx = b.gpr .edx; rw [d₁, d₂, ← p₁.a3, ← p₂.a3]
  exact b₁.seq (b₂.seq (b₃.seq b₄))

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn dgCode pn PublicKey.publicKeyExpanded) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  exact (body_ct s₁ _ _ _ _ _ _ ⟨s₁, s₂, pre_of h₁, pre_of h₂, Pub.refl s₁, pub_of hp, ctx_refl s₁,
    ctx_refl s₂, trivial, trivial⟩ e₁ e₂).1

/-! ## A witness, and the artifact's obligation -/

/-- The arguments at `0x8004`: `out` at `0x1000`, `expanded` at `0x2000`, the seed at `0x3000`
and `scratch` at `0x4000`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30
  else if a = 0x8011 then 0x40 else 0

def satState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemWith satArgs
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 16⟩]
  syms _ := 0x100000

theorem sat_arg (j : Nat) (hj : j < 4) : arg satState j = satArgs.readW (argAddr satState j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMemWith satArgs _ = _
  rw [satMemWith_out]
  have : ∀ j < 4, ∀ b < 4, 8 * 32 * 96 ≤ (argAddr satState j + BitVec.ofNat 64 b - 0x100000).toNat := by
    decide
  exact this j hj b (by omega)

theorem sat_pre : Pre satState := by
  have hl := combWords_length
  have a0 : arg satState 0 = 0x1000 := (sat_arg 0 (by decide)).trans (by decide)
  have a1 : arg satState 1 = 0x2000 := (sat_arg 1 (by decide)).trans (by decide)
  have a2 : arg satState 2 = 0x3000 := (sat_arg 2 (by decide)).trans (by decide)
  have a3 : arg satState 3 = 0x4000 := (sat_arg 3 (by decide)).trans (by decide)
  have held : TblWords ((satState.syms combSym).setWidth 64) satState.mem := satMemWith_held satArgs
  refine ⟨by decide, by decide, ?_, ?_, held, by rw [hl]; decide, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [SEED, EXP, OUT, SCR, TB, ARGS, RET, STK, K, esp, a0, a1, a2, a3, hl]
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 16⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem verified {dn pn : String} :
    Verified X86.target (keyPair dn dgCode pn PublicKey.publicKeyExpanded) spec :=
  ⟨fun _ h => keyPair_ok h, keyPair_ct, ⟨_, spec_of sat_pre⟩⟩

end VG.Proof.Ed25519.X86.KeyPair
