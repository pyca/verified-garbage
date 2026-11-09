module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInit
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.CountedLoop
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86.Inline

/-! # `vg_rsa_generate_init` on i686

The scan of `e`'s octets (`scan_ok`), the status and the masks
(`status_ok`), and the words (`words_ok`), each run of straight-line code
writing the state's 32-bit slots; the words they leave are
`keySearchInit`'s (`result_post`). Its timing depends only on the public
arguments, which the loop's count is: a taint check.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.KeyInit

open VG VG.X86 VG.Proof.MlDsa.X86.Pack
open VG.Impl.RsaKeyGen.X86.KeyInit
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- What the function is given. -/
structure ABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s.rd = [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 56⟩]
  outE : (⟨(arg s 0).setWidth 64, 56⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  outArgs : (⟨(arg s 0).setWidth 64, 56⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 56⟩
  retE : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  outBound : (arg s 0).toNat + 56 ≤ 2 ^ 32
  eBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32

theorem abi_of {s : State} (h : (Spec.RsaKeyGen.keyInitContract abi).pre s) : ABI s := by
  sig_pre [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

abbrev B (s : State) : Addr := (arg s 0).setWidth 64
abbrev E (s : State) : Addr := (arg s 2).setWidth 64
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (E s) (arg s 3).toNat

theorem param_eq (i : Nat) : param i = at_ .esp (4 + 4 * i) := by
  simp only [param, argAt, Nat.mul_zero, Nat.add_zero]

theorem ea0 (s : State) : (s.gpr .esp + BitVec.ofNat 32 4).setWidth 64 = argAddr s 0 := rfl
theorem ea1 (s : State) : (s.gpr .esp + BitVec.ofNat 32 8).setWidth 64 = argAddr s 1 := rfl
theorem ea2 (s : State) : (s.gpr .esp + BitVec.ofNat 32 12).setWidth 64 = argAddr s 2 := rfl
theorem ea3 (s : State) : (s.gpr .esp + BitVec.ofNat 32 16).setWidth 64 = argAddr s 3 := rfl

theorem ABI.argIn {s : State} (A : ABI s) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  have ai : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  rw [a0, ai]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem ABI.argRd {s : State} (A : ABI s) {i : Nat} (hi : i < 4) : InRegions (s.rd ++ s.wr) (argAddr s i) 4 :=
  ⟨⟨argAddr s 0, 16⟩, by rw [A.rd]; simp, A.argIn hi⟩

/-- The state's slot at byte `d`. -/
theorem ABI.eaS {s : State} (A : ABI s) {r : BitVec 32} (hr : r = arg s 0) {d : Nat} (hd : d < 56) :
    (r + BitVec.ofNat 32 d).setWidth 64 = B s + BitVec.ofNat 64 d := by
  rw [hr]; exact VG.Proof.MlKem.X86.ea_off (by have := A.outBound; omega)

theorem ABI.inW {s u : State} (A : ABI s) (hw : u.wr = s.wr) {d : Nat} (hd : d + 4 ≤ 56) :
    InRegions u.wr (B s + BitVec.ofNat 64 d) 4 :=
  ⟨_, by rw [hw, A.wr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩

theorem ABI.inRW {s u : State} (A : ABI s) (hw : u.wr = s.wr) {d : Nat} (hd : d + 4 ≤ 56) :
    InRegions (u.rd ++ u.wr) (B s + BitVec.ofNat 64 d) 4 :=
  let ⟨r, hr, hc⟩ := A.inW hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

theorem rdS (m : Mem) (B : Addr) (d : Nat) (v : BitVec 32) :
    (m.writeW (B + BitVec.ofNat 64 d) v).readW (B + BitVec.ofNat 64 d) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

theorem rdN (m : Mem) (B : Addr) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 64) (he : e < 64)
    (v : BitVec 32) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep B h (by omega) (by omega)) (by decide)

/-- A write to the state keeps everything outside it. -/
theorem frame_w {s : State} {m m' : Mem} (h : Frame [⟨B s, 56⟩] m m') {d : Nat} (hd : d + 4 ≤ 56)
    (v : BitVec 32) : Frame [⟨B s, 56⟩] m (m'.writeW (B s + BitVec.ofNat 64 d) v) :=
  h.writeW (List.mem_singleton_self _) v (Offset.contains_base _ (by omega) (by omega))

/-- An argument, through writes to the state. -/
theorem ABI.argKeep {s : State} (A : ABI s) {m : Mem} (h : Frame [⟨B s, 56⟩] s.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s i) 32 = arg s i :=
  (h.readW (A.argIn hi) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.outArgs.symm)
    (by decide)).trans rfl

/-- An argument, through a write to the state. -/
theorem ABI.argW {s : State} (A : ABI s) {i : Nat} (hi : i < 4) {d : Nat} (hd : d + 4 ≤ 56) (m : Mem)
    (v : BitVec 32) : (m.writeW (B s + BitVec.ofNat 64 d) v).readW (argAddr s i) 32 = m.readW (argAddr s i) 32 :=
  (frame_w (s := s) (Frame.refl _ m) hd v).readW (A.argIn hi)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.outArgs.symm) (by decide)

/-- An octet of `e`, through writes to the state. -/
theorem ABI.eKeep {s : State} (A : ABI s) {m : Mem} (h : Frame [⟨B s, 56⟩] s.mem m) {j : Nat}
    (hj : j < (arg s 3).toNat) : m (E s + BitVec.ofNat 64 j) = s.mem (E s + BitVec.ofNat 64 j) :=
  h _ fun r hr hc => by
    obtain rfl := List.mem_singleton.mp hr
    exact A.outE _ hc (Offset.contains_base _ (by omega) (by have := A.eBound; omega))

/-! ## The entry -/

theorem enter_ok {s : State} (A : ABI s) :
    WP isa (.block enter) s fun t =>
      (t.gpr .ebx = arg s 0 ∧ t.mem = ((s.mem.writeW (B s + BitVec.ofNat 64 0) (s.gpr .ebx)).writeW
        (B s + BitVec.ofNat 64 32) (0 : BitVec 32)).writeW (B s + BitVec.ofNat 64 36) (0 : BitVec 32)) ∧
        Keep [.eax, .ecx, .edx, .ebx] s t := by
  refine WP.keep _ ?_ (by rfl)
  simp only [enter, sb, param_eq, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, ea0, A.argRd (i := 0) (by decide), A.argKeep (Frame.refl _ _) (i := 0) (by decide),
    A.eaS rfl (d := 0) (by decide),
    A.eaS rfl (d := 32) (by decide), A.eaS rfl (d := 36) (by decide), A.inW rfl (d := 0) (by decide),
    A.inW rfl (d := 32) (by decide), A.inW rfl (d := 36) (by decide)]
  all_goals rfl

/-! ## The exponent's octets -/

theorem sub_one32 {k : Nat} (h1 : 1 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (2 ^ 32 - 1 + k % 2 ^ 32) % 2 ^ 32 = (k - 1) % 2 ^ 32
  omega

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this
  · rintro rfl; rfl

theorem add_one32 (P : BitVec 32) (j : Nat) : P + BitVec.ofNat 32 j + 1 = P + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem byteW (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat])

theorem dbl (x : BitVec 32) : x + x = BitVec.ofNat 32 (2 * x.toNat) :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem os2ip_snoc (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem or_eq_zero32 (x y : BitVec 32) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (·.getLsbD i) h <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem shr24_eq_zero {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 24 = 0 ↔ v < 2 ^ 24 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    change v / 2 ^ 24 = 0 at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    change v / 2 ^ 24 = 0
    omega

/-- After `j` of the `n` octets of `e`, with the memory after the entry. -/
structure ScanInv (s : State) (n j : Nat) (u : State) : Prop where
  ptr : u.gpr .ecx = arg s 2 + BitVec.ofNat 32 j
  cnt : u.gpr .edx = BitVec.ofNat 32 (n - j)
  z : u.zf = some (decide (n - j = 0))
  ebx : u.gpr .ebx = arg s 0
  val : u.mem.readW (B s + BitVec.ofNat 64 32) 32 =
    BitVec.ofNat 32 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E s) j) % 2 ^ 32)
  ovf : u.mem.readW (B s + BitVec.ofNat 64 36) 32 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E s) j) < 2 ^ 32
  saved : u.mem.readW (B s + BitVec.ofNat 64 0) 32 = s.gpr .ebx
  frame : Frame [⟨B s, 56⟩] s.mem u.mem
  keep : Keep [.eax, .ecx, .edx, .ebx] s u

theorem octet_ok {s u : State} (A : ABI s) {n j : Nat} (hj : j < n) (hn : n = (arg s 3).toNat)
    (h : ScanInv s n j u) : WP isa (.block octet) u (ScanInv s n (j + 1)) := by
  have eb := A.eBound
  have hw : u.wr = s.wr := h.keep.2.2
  have hr : u.rd = s.rd := h.keep.2.1
  have eaE : (arg s 2 + BitVec.ofNat 32 j + BitVec.ofNat 32 0).setWidth 64 = E s + BitVec.ofNat 64 j := by
    rw [BitVec.add_zero]; exact VG.Proof.MlKem.X86.ea_off (by omega)
  have rE : InRegions (u.rd ++ u.wr) (E s + BitVec.ofNat 64 j) 1 :=
    ⟨_, by rw [hr, A.rd]; exact List.mem_append_left _ (List.mem_cons_self ..),
      Offset.contains_base _ (by omega) (by omega)⟩
  have hb : u.mem (E s + BitVec.ofNat 64 j) = s.mem (E s + BitVec.ofNat 64 j) := A.eKeep h.frame (by omega)
  generalize hx : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E s) j) = x at h
  generalize ho : u.mem.readW (B s + BitVec.ofNat 64 36) 32 = o
  have hv := h.val
  have hs := h.saved
  have hv32 : x % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have byt := (s.mem (E s + BitVec.ofNat 64 j)).isLt
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (Q := fun t =>
      t.gpr .ecx = arg s 2 + BitVec.ofNat 32 (j + 1) ∧ t.gpr .edx = BitVec.ofNat 32 (n - (j + 1)) ∧
      t.zf = some (decide (n - (j + 1) = 0)) ∧
      t.mem = ((u.mem.writeW (B s + BitVec.ofNat 64 44) (BitVec.ofNat 32 (s.mem (E s + BitVec.ofNat 64 j)).toNat)).writeW
        (B s + BitVec.ofNat 64 36) ((BitVec.ofNat 32 (x % 2 ^ 32) >>> 24) ||| o)).writeW (B s + BitVec.ofNat 64 32)
        (BitVec.ofNat 32 ((256 * (x % 2 ^ 32) + (s.mem (E s + BitVec.ofNat 64 j)).toNat) % 2 ^ 32))) ?_ (by rfl))
    fun t ⟨⟨hc, hd, hz, hm⟩, k⟩ => ?_
  · unfold octet
    simp only [sb, List.cons_append, List.nil_append, List.replicate]
    have e44 := A.eaS rfl (d := 44) (by decide)
    have e36 := A.eaS rfl (d := 36) (by decide)
    have e32 := A.eaS rfl (d := 32) (by decide)
    xrun [State.ea, at_, h.ptr, h.cnt, h.ebx, eaE, rE, hb, e44, e36, e32, A.inW hw (d := 44) (by decide),
      A.inW hw (d := 36) (by decide), A.inW hw (d := 32) (by decide), A.inRW hw (d := 44) (by decide),
      A.inRW hw (d := 36) (by decide), A.inRW hw (d := 32) (by decide), rdS, rdN _ (B s) (d := 32) (e := 44)
      (by decide) (by decide) (by decide), rdN _ (B s) (d := 36) (e := 44) (by decide) (by decide) (by decide),
      rdN _ (B s) (d := 32) (e := 36) (by decide) (by decide) (by decide),
      rdN _ (B s) (d := 44) (e := 36) (by decide) (by decide) (by decide), hv, ho, byteW, add_one32,
      sub_one32 (k := n - j) (by omega) (by omega), show n - j - 1 = n - (j + 1) by omega,
      ofNat_beq (k := n - (j + 1)) (by omega)]
    rw [hx]
    refine congrArg (Mem.writeW _ _) ?_
    simp only [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  · have fr : Frame [⟨B s, 56⟩] s.mem t.mem := by
      rw [hm]; exact frame_w (frame_w (frame_w h.frame (by decide) _) (by decide) _) (by decide) _
    have snoc : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E s) (j + 1)) =
        256 * x + (s.mem (E s + BitVec.ofNat 64 j)).toNat := by
      rw [SearchInit.bytesAt_succ, os2ip_snoc, hx]
    refine ⟨hc, hd, hz, (k.gpr (by decide)).trans h.ebx, ?_, ?_, ?_, fr, (h.keep.trans k).mono (by simp)⟩
    · rw [hm, rdS, snoc]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [hm, rdN _ _ (by decide) (by decide) (by decide), rdS, or_eq_zero32, shr24_eq_zero hv32, ← ho,
        h.ovf, snoc]
      omega
    · rw [hm, rdN _ _ (by decide) (by decide) (by decide), rdN _ _ (by decide) (by decide) (by decide),
        rdN _ _ (by decide) (by decide) (by decide), hs]

theorem scan_ok {s u : State} (A : ABI s) (hb : u.gpr .ebx = arg s 0)
    (hm : u.mem = ((s.mem.writeW (B s + BitVec.ofNat 64 0) (s.gpr .ebx)).writeW
        (B s + BitVec.ofNat 64 32) (0 : BitVec 32)).writeW (B s + BitVec.ofNat 64 36) (0 : BitVec 32))
    (k : Keep [.eax, .ecx, .edx, .ebx] s u) :
    WP isa scan u (ScanInv s (arg s 3).toNat (arg s 3).toNat) := by
  have hw : u.wr = s.wr := k.2.2
  have hr : u.rd = s.rd := k.2.1
  have sp : u.gpr .esp = s.gpr .esp := k.gpr (by decide)
  have fr : Frame [⟨B s, 56⟩] s.mem u.mem := by
    rw [hm]; exact frame_w (frame_w (frame_w (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _
  have n32 := (arg s 3).isLt
  unfold scan
  refine WP.seq (WP.mono (WP.keep [.ecx, .edx] (Q := fun t =>
      t.gpr .ecx = arg s 2 ∧ t.gpr .edx = BitVec.ofNat 32 (arg s 3).toNat ∧
      t.zf = some (decide ((arg s 3).toNat = 0)) ∧ t.mem = u.mem) ?_ (by rfl))
    fun t ⟨⟨hc, hd, hz, htm⟩, kt⟩ => ?_)
  · simp only [param_eq, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, sp, ea2, ea3, hr, hw, A.argRd (i := 2) (by decide), A.argRd (i := 3) (by decide),
      A.argKeep fr (i := 2) (by decide), A.argKeep fr (i := 3) (by decide), BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.sub_zero, ofNat_beq n32]
    rw [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, BitVec.sub_zero, ← ofNat_beq n32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  have h0 : ScanInv s (arg s 3).toNat 0 t := by
    refine ⟨by rw [hc, BitVec.add_zero], by rw [hd, Nat.sub_zero], by rw [hz, Nat.sub_zero],
      (kt.gpr (by decide)).trans hb, ?_, ?_, ?_, by rw [htm]; exact fr, (k.trans kt).mono (by simp)⟩
    · rw [htm, hm, rdN _ _ (by decide) (by decide) (by decide), rdS]; rfl
    · rw [htm, hm, rdS]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip]
    · rw [htm, hm, rdN _ _ (by decide) (by decide) (by decide), rdN _ _ (by decide) (by decide) (by decide), rdS]
  refine WP.ite _ hz (fun hz' => ?_) (fun hz' => ?_)
  · have hz' : (arg s 3).toNat = 0 := of_decide_eq_true hz'
    exact WP.block_nil (by rw [hz'] at h0 ⊢; exact h0)
  · have hz' : (arg s 3).toNat ≠ 0 := of_decide_eq_false hz'
    refine WP.mono (WP.chunk_loop (I := fun j t => ScanInv s (arg s 3).toNat j t) (n := (arg s 3).toNat) (N := 1)
      (k := 0) (by decide) (by omega) h0 (fun j t hj ht => octet_ok A (by omega) rfl ht)
      (fun j t _ ht => ?_)) fun t ⟨j, hj, hl, ht⟩ => by
        obtain rfl : j = (arg s 3).toNat := by omega
        exact ht
    have e : isa.eval .ne t = some (!decide ((arg s 3).toNat - j = 0)) := by
      change t.zf.map (!·) = _; rw [ht.z]; rfl
    rw [e]
    constructor
    · intro hl; rw [decide_eq_true (by omega)]; rfl
    · intro hl; rw [decide_eq_false (by omega)]; rfl

/-! ## The status and the masks -/

/-- The mask of a borrow: all ones when `c`. -/
def mk (c : Bool) : BitVec 32 := if c then 4294967295 else 0

theorem mk_def (c : Bool) : 0#32 - BitVec.setWidth 32 (BitVec.ofBool c) = mk c := by cases c <;> rfl
theorem mk_not (c : Bool) : mk c ^^^ 4294967295 = mk (!c) := by cases c <;> rfl
theorem mk_or (a b : Bool) : mk a ||| mk b = mk (a || b) := by cases a <;> cases b <;> rfl

/-- The status, from whether the exponent and the size are refused. -/
def stat (a b : Bool) : BitVec 32 := if a then 0 else if b then 2 else 1

theorem mk_stat (a b : Bool) : (mk b &&& 1) + 1 &&& mk (!a) = stat a b := by cases a <;> cases b <;> rfl

theorem status_ok {s u : State} (A : ABI s) (hw : u.wr = s.wr) (hr : u.rd = s.rd) (sp : u.gpr .esp = s.gpr .esp)
    (hb : u.gpr .ebx = arg s 0) (fr : Frame [⟨B s, 56⟩] s.mem u.mem) {V o : BitVec 32}
    (hv : u.mem.readW (B s + BitVec.ofNat 64 32) 32 = V) (ho : u.mem.readW (B s + BitVec.ofNat 64 36) 32 = o) :
    let a := (!decide (o.toNat < 1) || decide ((V &&& 1).toNat < 1)) || decide (V.toNat < 3)
    let b := decide ((arg s 1).toNat < 512) || !decide ((arg s 1).toNat < 8193)
    WP isa (.block status) u fun t =>
      t.mem = (((u.mem.writeW (B s + BitVec.ofNat 64 40) (mk a)).writeW (B s + BitVec.ofNat 64 36)
        (mk (decide ((V ^^^ 3).toNat < 1)))).writeW (B s + BitVec.ofNat 64 44) (stat a b)).writeW
          (B s + BitVec.ofNat 64 40) (mk (!(b || a))) ∧ Keep [.eax, .ecx, .edx] u t := by
  intro a b
  refine WP.keep _ ?_ (by rfl)
  simp only [status, sb, param_eq, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, sp, ea1, hr, hw, hb, A.argRd (i := 1) (by decide), A.argKeep fr (i := 1) (by decide),
    A.eaS rfl (d := 32) (by decide), A.eaS rfl (d := 36) (by decide), A.eaS rfl (d := 40) (by decide),
    A.eaS rfl (d := 44) (by decide), A.inW (u := s) rfl (d := 36) (by decide), A.inW (u := s) rfl (d := 40) (by decide),
    A.inW (u := s) rfl (d := 44) (by decide), A.inRW (u := s) rfl (d := 32) (by decide),
    A.inRW (u := s) rfl (d := 36) (by decide), A.inRW (u := s) rfl (d := 40) (by decide), rdS,
    rdN _ (B s) (d := 40) (e := 36) (by decide) (by decide) (by decide),
    rdN _ (B s) (d := 40) (e := 44) (by decide) (by decide) (by decide), hv, ho, mk_def, mk_not, mk_or,
    A.argW (i := 1) (by decide) (d := 40) (by decide), A.argW (i := 1) (by decide) (d := 36) (by decide),
    show (1 : BitVec 32).toNat = 1 from rfl, show (3 : BitVec 32).toNat = 3 from rfl,
    show (512 : BitVec 32).toNat = 512 from rfl, show (8193 : BitVec 32).toNat = 8193 from rfl]
  simp only [mk_stat]
  rfl

/-! ## The words -/

/-- The slots `words` leaves: the masked words' low halves (slot 2 j), zero
high halves, and `e`'s octets in the last word. -/
structure Slots (s : State) (K T : Bool) (V : BitVec 32) (m : Mem) : Prop where
  w0 : m.readW (B s + BitVec.ofNat 64 0) 32 =
    BitVec.ofNat 32 (if K then (if T then 64 else 40) * ((arg s 1).toNat / 128 * 8) else 0)
  w1 : m.readW (B s + BitVec.ofNat 64 4) 32 = 0
  w2 : m.readW (B s + BitVec.ofNat 64 8) 32 = BitVec.ofNat 32 (if K then (arg s 1).toNat / 128 * 8 else 0)
  w3 : m.readW (B s + BitVec.ofNat 64 12) 32 = 0
  w4 : m.readW (B s + BitVec.ofNat 64 16) 32 =
    BitVec.ofNat 32 (if K then 32769 * ((arg s 1).toNat / 128 * 8) else 0)
  w5 : m.readW (B s + BitVec.ofNat 64 20) 32 = 0
  w6 : m.readW (B s + BitVec.ofNat 64 24) 32 = BitVec.ofNat 32 (if K then 32 * ((arg s 1).toNat / 128 * 8) else 0)
  w7 : m.readW (B s + BitVec.ofNat 64 28) 32 = 0
  w8 : m.readW (B s + BitVec.ofNat 64 32) 32 = 0
  w9 : m.readW (B s + BitVec.ofNat 64 36) 32 = 0
  w10 : m.readW (B s + BitVec.ofNat 64 40) 32 = BitVec.ofNat 32 (if K then 4 else 0)
  w11 : m.readW (B s + BitVec.ofNat 64 44) 32 = 0
  w12 : m.readW (B s + BitVec.ofNat 64 48) 32 = 0
  w13 : m.readW (B s + BitVec.ofNat 64 52) 32 = bswap (if K then V else 0)

theorem mk_true : mk true = 4294967295 := rfl
theorem mk_false : mk false = 0#32 := rfl
theorem and_ones (x : BitVec 32) : x &&& 4294967295 = x := by
  rw [show (4294967295 : BitVec 32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]

theorem words_ok {s w : State} (A : ABI s) (hw : w.wr = s.wr) (hr : w.rd = s.rd) (sp : w.gpr .esp = s.gpr .esp)
    (hb : w.gpr .ebx = arg s 0) (fr : Frame [⟨B s, 56⟩] s.mem w.mem) {K T : Bool} {V st : BitVec 32}
    (hV : w.mem.readW (B s + BitVec.ofNat 64 32) 32 = V) (hT : w.mem.readW (B s + BitVec.ofNat 64 36) 32 = mk T)
    (hK : w.mem.readW (B s + BitVec.ofNat 64 40) 32 = mk K) (hst : w.mem.readW (B s + BitVec.ofNat 64 44) 32 = st)
    (hsv : w.mem.readW (B s + BitVec.ofNat 64 0) 32 = s.gpr .ebx) :
    WP isa (.block words) w fun t =>
      (t.gpr .eax = st ∧ t.gpr .ebx = s.gpr .ebx ∧ Slots s K T V t.mem) ∧ Keep [.eax, .ecx, .edx, .ebx] w t := by
  have b32 := (arg s 1).isLt
  refine WP.keep _ ?_ (by rfl)
  simp only [words, sb, param_eq, Nat.reduceMul, Nat.reduceAdd]
  cases K <;> cases T <;>
  xrun [State.ea, at_, sp, ea0, ea1, hr, hw, hb, A.argRd (i := 0) (by decide), A.argRd (i := 1) (by decide),
    A.argKeep fr (i := 0) (by decide), A.argKeep fr (i := 1) (by decide),
    A.eaS rfl (d := 0) (by decide), A.eaS rfl (d := 4) (by decide), A.eaS rfl (d := 8) (by decide),
    A.eaS rfl (d := 12) (by decide), A.eaS rfl (d := 16) (by decide), A.eaS rfl (d := 20) (by decide),
    A.eaS rfl (d := 24) (by decide), A.eaS rfl (d := 28) (by decide), A.eaS rfl (d := 32) (by decide),
    A.eaS rfl (d := 36) (by decide), A.eaS rfl (d := 40) (by decide), A.eaS rfl (d := 44) (by decide),
    A.eaS rfl (d := 48) (by decide), A.eaS rfl (d := 52) (by decide),
    A.inW (u := s) rfl (d := 0) (by decide), A.inW (u := s) rfl (d := 4) (by decide),
    A.inW (u := s) rfl (d := 8) (by decide), A.inW (u := s) rfl (d := 12) (by decide),
    A.inW (u := s) rfl (d := 16) (by decide), A.inW (u := s) rfl (d := 20) (by decide),
    A.inW (u := s) rfl (d := 24) (by decide), A.inW (u := s) rfl (d := 28) (by decide),
    A.inW (u := s) rfl (d := 32) (by decide), A.inW (u := s) rfl (d := 36) (by decide),
    A.inW (u := s) rfl (d := 40) (by decide), A.inW (u := s) rfl (d := 44) (by decide),
    A.inW (u := s) rfl (d := 48) (by decide), A.inW (u := s) rfl (d := 52) (by decide),
    A.inRW (u := s) rfl (d := 0) (by decide), A.inRW (u := s) rfl (d := 32) (by decide),
    A.inRW (u := s) rfl (d := 36) (by decide), A.inRW (u := s) rfl (d := 40) (by decide),
    A.inRW (u := s) rfl (d := 44) (by decide), execMul, A.argW (i := 0) (by decide) (d := 8) (by decide), A.argW (i := 0) (by decide) (d := 4) (by decide), A.argW (i := 0) (by decide) (d := 12) (by decide), A.argW (i := 0) (by decide) (d := 20) (by decide), A.argW (i := 0) (by decide) (d := 28) (by decide), A.argW (i := 0) (by decide) (d := 48) (by decide), A.argW (i := 0) (by decide) (d := 16) (by decide), A.argW (i := 0) (by decide) (d := 24) (by decide), A.argW (i := 0) (by decide) (d := 36) (by decide), A.argW (i := 0) (by decide) (d := 52) (by decide), A.argW (i := 0) (by decide) (d := 40) (by decide), A.argW (i := 0) (by decide) (d := 32) (by decide), A.argW (i := 0) (by decide) (d := 44) (by decide)]
  all_goals refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  all_goals try constructor
  all_goals simp (disch := decide) only [rdS, rdN, hV, hT, hK, hst, hsv, mk_true, mk_false, and_ones,
    BitVec.and_zero, ↓reduceIte, Bool.false_eq_true]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq
       try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
         show (40 : BitVec 32).toNat = 40 from rfl, show (32769 : BitVec 32).toNat = 32769 from rfl]
       omega)

/-! ## The whole initialization -/

/-- What the function leaves, for the value `x` of `e` and the size. -/
def InitPost (s t : State) : Prop :=
  Keep [.eax, .ecx, .edx, .ebx] s t ∧ t.gpr .ebx = s.gpr .ebx ∧
    ∃ o : BitVec 32, (o = 0 ↔ Spec.Rsa.os2ip (eB s) < 2 ^ 32) ∧
      let V := BitVec.ofNat 32 (Spec.Rsa.os2ip (eB s) % 2 ^ 32)
      let a := (!decide (o.toNat < 1) || decide ((V &&& 1).toNat < 1)) || decide (V.toNat < 3)
      let b := decide ((arg s 1).toNat < 512) || !decide ((arg s 1).toNat < 8193)
      t.gpr .eax = stat a b ∧ Slots s (!(b || a)) (decide ((V ^^^ 3).toNat < 1)) V t.mem

theorem init_ok {s : State} (A : ABI s) : WP isa init s (InitPost s) := by
  unfold init
  refine WP.seq (WP.mono (enter_ok A) fun u ⟨⟨hb, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (scan_ok A hb hm k) fun v hv => ?_)
  rw [WP.block_append_iff]
  have hw : v.wr = s.wr := hv.keep.2.2
  have hr : v.rd = s.rd := hv.keep.2.1
  have sp : v.gpr .esp = s.gpr .esp := hv.keep.gpr (by decide)
  refine WP.mono (status_ok A hw hr sp hv.ebx hv.frame hv.val rfl) fun w ⟨hmw, kw⟩ => ?_
  have hw' : w.wr = s.wr := kw.2.2.trans hw
  have hr' : w.rd = s.rd := kw.2.1.trans hr
  have sp' : w.gpr .esp = s.gpr .esp := (kw.gpr (by decide)).trans sp
  have hb' : w.gpr .ebx = arg s 0 := (kw.gpr (by decide)).trans hv.ebx
  have fr' : Frame [⟨B s, 56⟩] s.mem w.mem := by
    rw [hmw]
    exact frame_w (frame_w (frame_w (frame_w hv.frame (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have hV : w.mem.readW (B s + BitVec.ofNat 64 32) 32 =
      BitVec.ofNat 32 (Spec.Rsa.os2ip (eB s) % 2 ^ 32) := by
    rw [hmw]; simp (disch := decide) only [rdN]; exact hv.val
  have hsv : w.mem.readW (B s + BitVec.ofNat 64 0) 32 = s.gpr .ebx := by
    rw [hmw]; simp (disch := decide) only [rdN]; exact hv.saved
  let V := BitVec.ofNat 32 (Spec.Rsa.os2ip (eB s) % 2 ^ 32)
  let o := v.mem.readW (B s + BitVec.ofNat 64 36) 32
  let a := (!decide (o.toNat < 1) || decide ((V &&& 1).toNat < 1)) || decide (V.toNat < 3)
  let b := decide ((arg s 1).toNat < 512) || !decide ((arg s 1).toNat < 8193)
  refine WP.mono (words_ok (K := !(b || a)) (T := decide ((V ^^^ 3).toNat < 1)) (st := stat a b)
    A hw' hr' sp' hb' fr' hV ?_ ?_ ?_ hsv) ?_
  · rw [hmw]; simp (disch := decide) only [rdS, rdN]; rfl
  · rw [hmw]; simp (disch := decide) only [rdS]; rfl
  · rw [hmw]; simp (disch := decide) only [rdS, rdN]; rfl
  intro t ⟨⟨hax, hbx, hS⟩, kt⟩
  exact ⟨((hv.keep.trans kw).trans kt).mono (by simp), hbx, _, hv.ovf, hax, hS⟩

/-! ## The contract -/

theorem word_at (m : Mem) (B : Addr) (i : Nat) :
    m.readW (B + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (B + BitVec.ofNat 64 (8 * i + 4)) 32 ++ m.readW (B + BitVec.ofNat 64 (8 * i)) 32 := by
  rw [Proof.Ffdh.X86.KeyInit.readW64_split, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem words7 (m : Mem) (B : Addr) : Spec.Rsa.wordsAt m B 7 =
    [m.readW (B + BitVec.ofNat 64 4) 32 ++ m.readW (B + BitVec.ofNat 64 0) 32,
      m.readW (B + BitVec.ofNat 64 12) 32 ++ m.readW (B + BitVec.ofNat 64 8) 32,
      m.readW (B + BitVec.ofNat 64 20) 32 ++ m.readW (B + BitVec.ofNat 64 16) 32,
      m.readW (B + BitVec.ofNat 64 28) 32 ++ m.readW (B + BitVec.ofNat 64 24) 32,
      m.readW (B + BitVec.ofNat 64 36) 32 ++ m.readW (B + BitVec.ofNat 64 32) 32,
      m.readW (B + BitVec.ofNat 64 44) 32 ++ m.readW (B + BitVec.ofNat 64 40) 32,
      m.readW (B + BitVec.ofNat 64 52) 32 ++ m.readW (B + BitVec.ofNat 64 48) 32] := by
  change [m.readW (B + BitVec.ofNat 64 (8 * 0)) 64, m.readW (B + BitVec.ofNat 64 (8 * 1)) 64,
    m.readW (B + BitVec.ofNat 64 (8 * 2)) 64, m.readW (B + BitVec.ofNat 64 (8 * 3)) 64,
    m.readW (B + BitVec.ofNat 64 (8 * 4)) 64, m.readW (B + BitVec.ofNat 64 (8 * 5)) 64,
    m.readW (B + BitVec.ofNat 64 (8 * 6)) 64] = _
  simp only [word_at]

theorem words6 (m : Mem) (B : Addr) : Spec.Rsa.wordsAt m B 6 = (Spec.Rsa.wordsAt m B 7).take 6 := by
  simp only [Spec.Rsa.wordsAt]; rfl

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem bswap_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (bswap x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact bswap_bit x hb hi

theorem byte_ofNat {x : Nat} (hx : x < 2 ^ 32) {k : Nat} (_hk : k < 4) :
    (BitVec.ofNat 32 x).extractLsb' (8 * k) 8 = BitVec.ofNat 8 (x / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, show 2 ^ (8 * k) = 256 ^ k by rw [Nat.pow_mul]]

/-- `e`'s eight octets, most significant first: four zeros, then its 32-bit
value's, from the byte-swapped word. -/
theorem e_bytes (m : Mem) (B : Addr) {x : Nat} (hx : x < 2 ^ 32)
    (h12 : m.readW (B + BitVec.ofNat 64 48) 32 = 0)
    (h13 : m.readW (B + BitVec.ofNat 64 52) 32 = bswap (BitVec.ofNat 32 x)) :
    Spec.Rsa.bytesAt m (B + 48) 8 = Spec.Rsa.i2osp x 8 := by
  have lo (i : Nat) (hi : i < 4) : m ((B + 48) + BitVec.ofNat 64 i) = BitVec.ofNat 8 (x / 256 ^ (8 - 1 - i)) := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, Mem.readW_byte m _ hi, h12]
    rw [Nat.div_eq_of_lt (show x < 256 ^ (8 - 1 - i) by
      calc x < 256 ^ 4 := by omega
        _ ≤ 256 ^ (8 - 1 - i) := Nat.pow_le_pow_right (by decide) (by omega))]
    exact BitVec.eq_of_toNat_eq (by simp)
  have hi (j : Nat) (hj : j < 4) : m ((B + 48) + BitVec.ofNat 64 (4 + j)) = BitVec.ofNat 8 (x / 256 ^ (8 - 1 - (4 + j))) := by
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 48 + (4 + j) = 52 + j by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Mem.readW_byte m _ hj, h13,
      bswap_byte _ hj, byte_ofNat hx (by omega), show 8 - 1 - (4 + j) = 3 - j by omega]
  simp only [Spec.Rsa.bytesAt, Spec.Rsa.i2osp]
  change [m ((B + 48) + BitVec.ofNat 64 0), m ((B + 48) + BitVec.ofNat 64 1), m ((B + 48) + BitVec.ofNat 64 2),
    m ((B + 48) + BitVec.ofNat 64 3), m ((B + 48) + BitVec.ofNat 64 4), m ((B + 48) + BitVec.ofNat 64 5),
    m ((B + 48) + BitVec.ofNat 64 6), m ((B + 48) + BitVec.ofNat 64 7)] =
    [BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 0)), BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 1)),
      BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 2)), BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 3)),
      BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 4)), BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 5)),
      BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 6)), BitVec.ofNat 8 (x / 256 ^ (8 - 1 - 7))]
  rw [lo 0 (by decide), lo 1 (by decide), lo 2 (by decide), lo 3 (by decide), hi 0 (by decide),
    hi 1 (by decide), hi 2 (by decide), hi 3 (by decide)]

theorem lt_one_iff (o : BitVec 32) : decide (o.toNat < 1) = decide (o = 0) := by
  apply decide_eq_decide.mpr
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega)
  · rintro rfl; decide

theorem and1_toNat (V : BitVec 32) : (V &&& 1).toNat = V.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem xor3_lt (V : BitVec 32) : decide ((V ^^^ 3).toNat < 1) = decide (V = 3) := by
  rw [lt_one_iff]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    have := congrArg (· ^^^ (3 : BitVec 32)) h
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
    exact this
  · rintro rfl; decide

/-- The exponent is refused exactly when `keySearchInit` refuses it. -/
theorem a_eq {o : BitVec 32} {x : Nat} (ho : o = 0 ↔ x < 2 ^ 32) :
    ((!decide (o.toNat < 1) || decide ((BitVec.ofNat 32 (x % 2 ^ 32) &&& 1).toNat < 1)) ||
      decide ((BitVec.ofNat 32 (x % 2 ^ 32)).toNat < 3)) = !Spec.RsaKeyGen.exponentValid x := by
  rw [lt_one_iff, and1_toNat, BitVec.toNat_ofNat]
  unfold Spec.RsaKeyGen.exponentValid
  by_cases hx : x < 2 ^ 32
  · rw [decide_eq_true (ho.mpr hx), Nat.mod_mod, Nat.mod_eq_of_lt hx]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> by_cases h3 : 3 ≤ x <;>
      simp [h, h3, hx] <;> omega
  · rw [decide_eq_false (fun h => hx (ho.mp h))]
    simp [hx]

theorem b_eq (bits : Nat) :
    (decide (bits < 512) || !decide (bits < 8193)) = (Spec.RsaKeyGen.modulusBits bits).isNone := by
  unfold Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits Spec.RsaKeyGen.minBits
  by_cases h1 : 8192 < bits
  · simp [h1]; omega
  · by_cases h2 : bits / 128 * 128 < 512
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega

theorem bswap_zero : bswap (0 : BitVec 32) = 0 := by decide

theorem result_post {s t : State} (P : InitPost s t) :
    match Spec.RsaKeyGen.keySearchInit (arg s 1).toNat (eB s) with
    | .error c => (t.gpr .eax).toNat = c ∧ Spec.Rsa.wordsAt t.mem (B s) 7 = List.replicate 7 0
    | .ok values => (t.gpr .eax).toNat = 1 ∧ ∃ first,
        Spec.Rsa.wordsAt t.mem (B s) 6 = (values ++ [first, 0, Spec.RsaKeyGen.keyGenerations]).map (BitVec.ofNat 64) ∧
        Spec.Rsa.bytesAt t.mem (B s + 48) 8 = Spec.Rsa.i2osp (Spec.Rsa.os2ip (eB s)) 8 ∧
        Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (values.getD 1 0)) 0 first := by
  obtain ⟨-, -, o, ho, hax, S⟩ := P
  generalize hx : Spec.Rsa.os2ip (eB s) = x at ho hax S ⊢
  have b32 := (arg s 1).isLt
  rw [a_eq ho, b_eq] at hax S
  rw [xor3_lt] at S
  unfold Spec.RsaKeyGen.keySearchInit
  rw [hx]
  have W := words7 t.mem (B s)
  rw [S.w0, S.w1, S.w2, S.w3, S.w4, S.w5, S.w6, S.w7, S.w8, S.w9, S.w10, S.w11, S.w12, S.w13] at W
  by_cases hv : Spec.RsaKeyGen.exponentValid x = true
  · rw [hv] at hax W S
    simp only [Bool.not_true, Bool.or_false, Bool.not_eq_true'] at hax W S
    have hvE : x % 2 = 1 ∧ 3 ≤ x ∧ x < 2 ^ 32 := by
      unfold Spec.RsaKeyGen.exponentValid at hv
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      omega
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hmb : Spec.RsaKeyGen.modulusBits (arg s 1).toNat with
    | none =>
      rw [hmb] at hax W
      simp only [Option.isNone_none, ↓reduceIte, Bool.true_eq_false] at hax W
      refine ⟨by rw [hax]; rfl, ?_⟩
      rw [W, bswap_zero]
      rfl
    | some nlen =>
      rw [hmb] at hax W S
      simp only [Option.isNone_some, Bool.not_false, ↓reduceIte] at hax W S
      have hn : 512 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 8192 ∧ nlen = (arg s 1).toNat / 128 * 128 := by
        unfold Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits Spec.RsaKeyGen.minBits at hmb
        by_cases h1 : 8192 < (arg s 1).toNat
        · simp [h1] at hmb
        · by_cases h2 : (arg s 1).toNat / 128 * 128 < 512
          · simp [h1, h2] at hmb
          · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hmb
            omega
      have hP : nlen / 16 = (arg s 1).toNat / 128 * 8 := by omega
      refine ⟨by rw [hax]; rfl, 32 * ((arg s 1).toNat / 128 * 8), ?_, ?_, ?_⟩
      · rw [words6, W]
        have hx3 : decide (BitVec.ofNat 32 (x % 2 ^ 32) = 3) = decide (x = 3) := by
          apply decide_eq_decide.mpr
          rw [Nat.mod_eq_of_lt hvE.2.2]
          constructor
          · intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvE.2.2] at this; exact this
          · rintro rfl; rfl
        simp only [hx3, hP, List.take, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          Spec.RsaKeyGen.keyGenerations, Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeEntropy,
          List.cons.injEq, and_true]
        by_cases h3 : x = 3 <;> simp only [h3, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (rw [show (0 : BitVec 32) = 0#32 from rfl]
           first | rfl | exact Proof.Ffdh.X86.ParamInit.zero_half (by omega) |
            (rw [Proof.Ffdh.X86.ParamInit.zero_half (by omega)]; congr 1; omega))
      · exact e_bytes _ _ hvE.2.2 S.w12 (by rw [S.w13]; simp only [↓reduceIte, Nat.mod_eq_of_lt hvE.2.2])
      · simp only [List.getD_cons_zero, List.getD_cons_succ, hP]
        unfold Spec.Entropy.RequestValid Spec.RsaKeyGen.primeEntropy
        omega
  · have hv' : Spec.RsaKeyGen.exponentValid x = false := by simpa using hv
    rw [hv'] at hax W
    simp only [Bool.not_false, Bool.or_true, Bool.not_true, ↓reduceIte, Bool.false_eq_true] at hax W
    simp only [hv', Bool.not_false, ↓reduceIte]
    refine ⟨by rw [hax]; rfl, ?_⟩
    rw [W, bswap_zero]
    rfl

theorem correct (s : State) (h : (Spec.RsaKeyGen.keyInitContract abi).pre s) :
    ∃ trace t, Exec isa init s trace t ∧ abiPreserved s t ∧ (Spec.RsaKeyGen.keyInitContract abi).post s t := by
  have A := abi_of h
  obtain ⟨tr, t, E, P⟩ := init_ok A
  have R := (Exec.regions E (by rfl)).2.2
  refine ⟨tr, t, E, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hb : r = .ebx
    · subst hb; exact P.2.1
    · exact P.1.gpr (by revert r; decide)
  · exact R.readW (Region.contains_self _ _) (fun r hr => by
      rw [A.wr] at hr; obtain rfl := List.mem_singleton.mp hr; exact A.retOut) (by decide)
  · sig_post [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    exact result_post P

theorem args_out {s : State} (A : ABI s) : ArgsOut 4 s := by
  refine ⟨A.stackBound, fun r hr => ?_⟩
  rw [A.wr] at hr
  obtain rfl := List.mem_singleton.mp hr
  intro a ha hb
  let j := (a - (s.gpr .esp).setWidth 64).toNat
  have hj : j < 20 := by change j + 1 ≤ 20 at ha; omega
  have he : (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j = a := by
    change (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (a - (s.gpr .esp).setWidth 64).toNat = a
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  by_cases h : j < 4
  · exact A.retOut a (by rw [← he]; exact Offset.contains_base _ (by omega) (by omega)) hb
  · exact A.outArgs a hb (by rw [a0, ← he]; exact Offset.contains _ (by omega) (by omega) (by decide))

theorem constantTime : ConstantTime isa (Spec.RsaKeyGen.keyInitContract abi).pre
    (Spec.RsaKeyGen.keyInitContract abi).pub init := by
  refine VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 20) ?_ (by taint_decide)
  intro s t hs ht H
  sig_pub [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, -, a0, a1, a2, a3⟩ := H
  refine agree_argTaint (k := 4) (fun _ h => nomatch h) SP (args_out (abi_of hs)) (args_out (abi_of ht)) ?_
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

/-- The state at `0x1000`, 2048 bits, `e = 3` (three octets) at `0x2000`, the arguments at `0x4004`. -/
def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x08 else if a = 0x400D then 0x20 else
    if a = 0x4010 then 3 else 0
  rd := [⟨0x2000, 3⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 56⟩]

theorem satisfiable : ∃ s, (Spec.RsaKeyGen.keyInitContract abi).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a2 : arg satState 2 = 0x2000 := by decide
  have a3 : arg satState 3 = 3 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  have esp : satState.gpr .esp = 0x4000 := rfl
  sig_implies_sat [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig, abi, argSlots, argVal,
    argBytes, stackBelow] [a0, a2, a3, e, esp, satState] using satState

theorem init_verified : Verified target init (Spec.RsaKeyGen.keyInitContract abi) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.KeyInit
