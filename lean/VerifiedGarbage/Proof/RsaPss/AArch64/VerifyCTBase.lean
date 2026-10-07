import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyTop
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit

/-!
# RSASSA-PSS verification on AArch64: constant time, the public data and the checks

The pointers, the lengths, the bytes of `n` and `e` and the precomputed
values are public (`PubV`, from `verifyPrecomputedContract.pub`); the digest
and the signature are secret. Two runs with the same public data as an
anchor `a` (`E`) are related at each point of the code by what correctness
says there. The checks of the modulus' first byte and of the lengths branch
on public values only (`AtEV`, `AtSV`: the states after `emLen` and
`saltFits`); the expected salt length is chosen by `any_salt_len`, loaded
from its slot and public by correctness (`expLen_ct`).
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_ite wp_ldrSp)
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (stackArgs_five)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV smear_ok emLen_ok expLen_ok two_taintE zH two_step pins_nil)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0 setWidth_byte maskV_setWidth in_frame bytesAt_cons)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, the bytes of `n` and `e`, and the precomputed values. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  a0 : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32
  args : ∀ i, 0 < i → i < 5 → stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x0) (a.gpr .x1).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem PubV.refl (s : State) : PubV s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq2 {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

theorem pubV_of (G : Spec.Mgf1.Hash) {S : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPss.verifyPrecomputedContract G G abi S).pub s₁ s₂) : PubV s₁ s₂ := by
  sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, stackArgs_five,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨hne, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h1, h3])
  obtain ⟨hn, he⟩ := leak_eq2 (by rw [bytesAt_length, bytesAt_length, h1]) hne
  refine ⟨hsp.symm, fun r hr => ?_, a0.symm, fun i hi hi' => ?_, hn.symm, he.symm,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw).symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    exacts [a1.symm, a2.symm, a3.symm, a4.symm]

/-- An entry state with the anchor's public data. -/
def E (D K : Nat) (a s : State) : Prop := PreV D K s ∧ PubV a s

/-- `J` at a point of the code, from an entry state with the anchor `a`'s
public data. -/
def At (D K : Nat) (J : State → State → Prop) (a t : State) : Prop := ∃ s, E D K a s ∧ J s t

/-- The first byte of `n`. -/
abbrev nxV (s : State) : Nat := (s.mem (s.gpr .x0)).toNat

namespace E
variable {D K : Nat} {a s : State} (h : E D K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem scr : scr s = scr a := h.2.args 1 (by decide) (by decide)

theorem k : (s.gpr .x1).toNat = (a.gpr .x1).toNat := by rw [h.gpr (r := .x1) (by decide)]

theorem n0 : s.mem (s.gpr .x0) = a.mem (a.gpr .x0) := by
  have hk := h.1.k1
  have e1 := h.gpr (r := .x1) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x0) (k := (s.gpr .x1).toNat) (by omega),
    bytesAt_cons a.mem (a.gpr .x0) (k := (a.gpr .x1).toNat) (by rw [← e1]; omega)] at this
  exact (List.cons.inj this).1

theorem nx : nxV s = nxV a := congrArg BitVec.toNat h.n0

theorem any : anyV s = anyV a := by rw [anyV, anyV, h.2.a0]

theorem sLen : sLenV s = sLenV a := by rw [sLenV, sLenV, h.any, h.gpr (r := .x7) (by decide)]

end E

/-! ## A failed check -/

/-- 0 returned. -/
theorem vfail_ct {D K : Nat} {Φ : State → State → Prop} (hΦ : ∀ a u, Φ a u → ∃ s, E D K a s ∧ Mid s u) :
    RelCT isa (Two Φ) verifyFail (Two fun a t => t.sp = fb a) :=
  two_post (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by
      obtain ⟨_, e₁, m₁⟩ := hΦ a s₁ h₁
      obtain ⟨_, e₂, m₂⟩ := hΦ a s₂ h₂
      rw [m₁.sp, m₂.sp, e₁.fb, e₂.fb]) (by taint_decide))
    fun a u h => by
      obtain ⟨s, e, m⟩ := hΦ a u h
      exact WP.mono (fail_ok m) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]

/-! ## The checks -/

/-- After `emLen`: the mask and `lo` in their slots, `emLen` in `x9`, and
`x10` nonzero if it is less than `hLen + 2`. -/
structure AtEV (D : Nat) (s u : State) : Prop where
  m : Mid s u
  h0 : nxV s ≠ 0
  x19 : u.gpr .x19 = off (scr s) oSt
  x20 : u.gpr .x20 = scr s
  x21 : u.gpr .x21 = off (scr s) oDig
  x23 : u.gpr .x23 = s.gpr .x1
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  lo : u.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 (loV (nxV s))
  c : u.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = maskV (nxV s)
  x9 : u.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - loV (nxV s))
  x10 : (u.gpr .x10 != 0) = decide ((s.gpr .x1).toNat - loV (nxV s) < D + 2)

theorem chk1_ok (H : Hash) (hD : H.D + 2 < 4096) {K : Nat} {s u : State} (hp : PreV H.D K s) (hu : AtChk s u)
    (h0 : nxV s ≠ 0) :
    WP isa (.seq (.block smear) (emLen H)) u (AtEV H.D s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have Mu : Mid s u := ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (nxV s) := by rw [hu.x10, setWidth_byte]
  have hn₀ := (s.mem (s.gpr .x0)).isLt
  refine WP.seq (WP.mono (smear_ok u (x := nxV s) hn₀ h0 hx10) fun u₁ ⟨O₁, h11⟩ => ?_)
  refine WP.mono (emLen_ok H hD (F := fb s) (by rw [O₁.sp, hu.sp]) hn₀ h0
    (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide)) (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide))
    (k := (s.gpr .x1).toNat) (by rw [O₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)
    (by omega) h11) fun u₂ ⟨K₂, m₂, x9₂, x10₂⟩ => ?_
  have hm₂ : u₂.mem = (u.mem.writeW (fb s + BitVec.ofNat 64 sC) (maskV (nxV s))).writeW (fb s + BitVec.ofNat 64 sLo)
      (BitVec.ofNat 64 (loV (nxV s))) := by rw [m₂, O₁.mem]
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
structure AtSV (D : Nat) (s w : State) : Prop where
  m : AtMain D s (loV (nxV s)) ((maskV (nxV s)).setWidth 8) w
  h0 : nxV s ≠ 0
  hk : ¬ (s.gpr .x1).toNat - loV (nxV s) < D + 2
  x10 : (w.gpr .x10 != 0) = decide ((s.gpr .x1).toNat - loV (nxV s) - (D + 2) < (sLenV s).getD 0)

theorem AtEV.lay {D K : Nat} {s u : State} (h : AtEV D s u) (hp : PreV D K s) (hK : 16 ≤ K) :
    Lay u (fb s) (scr s) :=
  rsa_lay hp hK h.m.sp h.m.wr h.x20

theorem AtEV.any {D : Nat} {s u : State} (h : AtEV D s u) : u.mem.readW (off (fb s) sAny) 64 = anyV s := h.m.fr.any

theorem AtEV.sl {D : Nat} {s u : State} (h : AtEV D s u) : u.mem.readW (off (fb s) sSaltLen) 64 = s.gpr .x7 :=
  h.m.fr.rs (.x7, sSaltLen) (by simp [regSlots])

theorem chk2_ok (H : Hash) (hD : H.D + 2 < 4096) {K : Nat} {s u : State} (hp : PreV H.D K s) (hK : 16 ≤ K)
    (hu : AtEV H.D s u) (hk : ¬ (s.gpr .x1).toNat - loV (nxV s) < H.D + 2) :
    WP isa (.seq expLen (.block (saltFits H))) u (AtSV H.D s) := by
  have hk2 := hp.k2
  have hn₀ := (s.mem (s.gpr .x0)).isLt
  refine WP.seq (WP.mono (expLen_ok (hu.lay hp hK) hu.any hu.sl) fun u₃ ⟨O₃, x12₃⟩ => ?_)
  refine WP.mono (saltFitsR_ok H hD (a := (s.gpr .x1).toNat - loV (nxV s)) (by omega) (by omega)
    (by rw [O₃.get .x9, hu.x9]) x12₃) fun u₄ ⟨O₄, x9₄, x10₄⟩ => ?_
  have hsv : (if anyV s = 0 then s.gpr .x7 else 0).toNat = (sLenV s).getD 0 := by
    unfold sLenV; split <;> rfl
  rw [hsv] at x10₄
  have O : Only [.x13, .x12, .x9, .x10] u u₄ := (O₃.trans O₄).mono
  exact ⟨{
    sp := O.sp.trans hu.m.sp
    rd := O.rd.trans hu.m.rd
    wr := O.wr.trans hu.m.wr
    x9 := x9₄
    x19 := by rw [O.get .x19, hu.x19]
    x20 := by rw [O.get .x20, hu.x20]
    x21 := by rw [O.get .x21, hu.x21]
    x23 := by rw [O.get .x23, hu.x23]
    v := fun r hr => (O.vcs r hr).trans (hu.m.v r hr)
    mem := O.mem ▸ hu.mem
    fr := O.mem ▸ hu.m.fr
    lo := by rw [O.mem]; exact hu.lo
    c := by rw [O.mem, hu.c, ← maskV_setWidth _ hn₀] }, hu.h0, hk, x10₄⟩

/-- `expLen`: `any_salt_len` is loaded from its slot, and branched on. -/
theorem expLen_ct {D K : Nat} (hK : 16 ≤ K) :
    RelCT isa (Two fun a u => (∃ s, E D K a s ∧ AtEV D s u) ∧ isa.eval (.nonzero .x .x10) u = some false) expLen
      (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u ⟨⟨s, e, hu⟩, _⟩ =>
    WP.mono (expLen_ok (hu.lay e.1 hK) hu.any hu.sl) fun t ⟨O, _⟩ => by rw [O.sp, hu.m.sp, e.fb]
  unfold expLen
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → t.sp = fb a) → Pins Φ [] := fun h =>
    pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h a s₁ h₁, h a s₂ h₂]
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x13 = anyV a)
    (two_taint [] (pin fun a t ⟨⟨s, e, hu⟩, _⟩ => by rw [hu.m.sp, e.fb]) (by taint_decide))
    (fun a u ⟨⟨s, e, hu⟩, _⟩ => ?_) ?_
  · unfold ld
    have hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 sAny) 8 := by
      rw [hu.m.sp, hu.m.rd, hu.m.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))
    refine wp_ldrSp (by decide) hin fun u' o x => wp_nil ⟨by rw [o.sp, hu.m.sp, e.fb], ?_⟩
    rw [x, hu.m.sp]; exact hu.m.fr.any.trans e.any
  refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
    (two_taint [] (pin fun a t h => h.1.1) (by taint_decide)) (two_taint [] (pin fun a t h => h.1.1) (by taint_decide))

end VG.Proof.RsaPss.AArch64.Vfy
