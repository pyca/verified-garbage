import VerifiedGarbage.Proof.RsaPss.AArch64.SignTop
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT

/-!
# RSASSA-PSS signing on AArch64: constant time, the public data and the checks

The pointers, the lengths and the bytes of `n` and `e` are public (`PubS`,
from `signContract.pub`); the digest, the salt and the private key are
secret. Two runs with the same public data as an anchor `a` (`E`) are
related at each point of the code by what correctness says there (`At`).
The checks of the modulus' first byte and of the lengths branch on public
values only (`AtE`, `AtS`: the states after `emLen` and `saltFits`).
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two Pins two_taint two_post two_ite wp_ldrSp wp_mov)
open VG.Proof.RsaPkcs1Sig.AArch64.Sgn (stackArgs_thirteen)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV smear_ok emLen_ok saltFits_ok two_taintE zH)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, and the bytes of `n` and `e`. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ i < 13, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat

theorem PubS.refl (s : State) : PubS s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem leak_eq2 {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

theorem pubS_of (G : Spec.Mgf1.Hash) {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPss.signContract G G abi S).pub s₁ s₂) :
    PubS s₁ s₂ := by
  sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  obtain ⟨hn, he⟩ := leak_eq2 (by rw [bytesAt_length, bytesAt_length, h3]) hl
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, hn.symm, he.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm,
      a10.symm, a11.symm, a12.symm]

/-- An entry state with the anchor's public data. -/
def E (D K : Nat) (a s : State) : Prop := PreS D K s ∧ PubS a s

/-- `J` at a point of the code, from an entry state with the anchor `a`'s
public data. -/
def At (D K : Nat) (J : State → State → Prop) (a t : State) : Prop := ∃ s, E D K a s ∧ J s t

namespace E
variable {D K : Nat} {a s : State} (h : E D K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem n0 : s.mem (s.gpr .x2) = a.mem (a.gpr .x2) := by
  have hk := h.1.k1
  have e3 := h.gpr (r := .x3) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x2) (k := (s.gpr .x3).toNat) (by omega),
    bytesAt_cons a.mem (a.gpr .x2) (k := (a.gpr .x3).toNat) (by rw [← e3]; omega)] at this
  exact (List.cons.inj this).1

theorem scr : scr s = scr a := h.2.args 11 (by decide)

end E

/-! ## The checks -/

/-- The first byte of `n`. -/
abbrev nx (s : State) : Nat := (s.mem (s.gpr .x2)).toNat

/-- After `emLen`: the mask and `lo` in their slots, `emLen` in `x9`, and
`x10` nonzero if it is less than `hLen + 2`. -/
structure AtE (D : Nat) (s u : State) : Prop where
  m : Mid s u
  h0 : nx s ≠ 0
  x19 : u.gpr .x19 = off (scr s) oSt
  x20 : u.gpr .x20 = scr s
  x21 : u.gpr .x21 = off (scr s) oDig
  x23 : u.gpr .x23 = s.gpr .x3
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  lo : u.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 (loV (nx s))
  c : u.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = maskV (nx s)
  x9 : u.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x3).toNat - loV (nx s))
  x10 : (u.gpr .x10 != 0) = decide ((s.gpr .x3).toNat - loV (nx s) < D + 2)

theorem chk1_ok (H : Hash) (hD : H.D + 2 < 4096) {K : Nat} {s u : State} (hp : PreS H.D K s) (hu : AtChk s u)
    (h0 : nx s ≠ 0) :
    WP isa (.seq (.block smear) (emLen H)) u (AtE H.D s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have Mu : Mid s u := ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (nx s) := by rw [hu.x10, setWidth_byte]
  have hn₀ := (s.mem (s.gpr .x2)).isLt
  refine WP.seq (WP.mono (smear_ok u (x := nx s) hn₀ h0 hx10) fun u₁ ⟨O₁, h11⟩ => ?_)
  refine WP.mono (emLen_ok H hD (F := fb s) (by rw [O₁.sp, hu.sp]) hn₀ h0
    (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide)) (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide))
    (k := (s.gpr .x3).toNat) (by rw [O₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)
    (by omega) h11) fun u₂ ⟨K₂, m₂, x9₂, x10₂⟩ => ?_
  have hm₂ : u₂.mem = (u.mem.writeW (fb s + BitVec.ofNat 64 sC) (maskV (nx s))).writeW (fb s + BitVec.ofNat 64 sLo)
      (BitVec.ofNat 64 (loV (nx s))) := by rw [m₂, O₁.mem]
  exact {
    m := mid_frame Mu (O₁.keep.trans K₂) (d₁ := sC) (d₂ := sLo) (by decide) (by decide) hm₂
    h0 := h0
    x19 := by rw [K₂.get .x19, O₁.get .x19, hu.x19]
    x20 := by rw [K₂.get .x20, O₁.get .x20, hu.x20]
    x21 := by rw [K₂.get .x21, O₁.get .x21, hu.x21]
    x23 := by rw [K₂.get .x23, O₁.get .x23, hu.x23]
    mem := by
      rw [hm₂]
      exact (hu.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    lo := by rw [hm₂, Mem.readW_writeW_self64]
    c := by
      rw [hm₂, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    x9 := x9₂
    x10 := x10₂ }

/-- After `saltFits`: `AtMain`, and `x10` nonzero if the salt does not fit. -/
structure AtS (D : Nat) (s w : State) : Prop where
  m : AtMain D s (loV (nx s)) ((maskV (nx s)).setWidth 8) w
  h0 : nx s ≠ 0
  hk : ¬ (s.gpr .x3).toNat - loV (nx s) < D + 2
  x10 : (w.gpr .x10 != 0) = decide ((s.gpr .x3).toNat - loV (nx s) - (D + 2) < (stackArg s 10).toNat)

theorem chk2_ok (H : Hash) (hD : H.D + 2 < 4096) {K : Nat} {s u : State} (hp : PreS H.D K s) (hu : AtE H.D s u)
    (hk : ¬ (s.gpr .x3).toNat - loV (nx s) < H.D + 2) :
    WP isa (.block ([ld .x12 sSaltLen] ++ saltFits H)) u (AtS H.D s) := by
  have hk2 := hp.k2
  have hn₀ := (s.mem (s.gpr .x2)).isLt
  refine WP.mono (saltFits_ok H hD (F := fb s) hu.m.sp
    (by rw [hu.m.rd, hu.m.wr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide)
      (by decide))))
    (a := (s.gpr .x3).toNat - loV (nx s)) (sl := (stackArg s 10).toNat) (by omega) (by omega) hu.x9
    (by rw [hu.m.fr.sl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (stackArg s 10).isLt)
    fun u₃ ⟨O₃, x9₃, x10₃⟩ => ⟨{
      sp := O₃.sp.trans hu.m.sp
      rd := O₃.rd.trans hu.m.rd
      wr := O₃.wr.trans hu.m.wr
      x9 := x9₃
      x19 := by rw [O₃.get .x19, hu.x19]
      x20 := by rw [O₃.get .x20, hu.x20]
      x21 := by rw [O₃.get .x21, hu.x21]
      x23 := by rw [O₃.get .x23, hu.x23]
      v := fun r hr => (O₃.vcs r hr).trans (hu.m.v r hr)
      mem := O₃.mem ▸ hu.mem
      fr := O₃.mem ▸ hu.m.fr
      lo := by rw [O₃.mem]; exact hu.lo
      c := by rw [O₃.mem, hu.c, ← maskV_setWidth _ hn₀] }, hu.h0, hk, x10₃⟩

end VG.Proof.RsaPss.AArch64.Sgn
